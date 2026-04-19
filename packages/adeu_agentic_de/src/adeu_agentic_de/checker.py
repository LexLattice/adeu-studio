from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

from adeu_agent_harness.worker_boundary_conformance import (
    WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA,
    WorkerBoundaryConformanceReport,
)
from adeu_agent_harness.worker_delegation_topology import (
    WORKER_DELEGATION_TOPOLOGY_SCHEMA,
    WorkerDelegationTopology,
)
from adeu_ir.repo import repo_root
from urm_runtime.models import (
    ConnectorSnapshotResponse,
    CopilotSessionSendRequest,
    CopilotTurnSnapshot,
)

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
    AGENTIC_DE_BRIDGE_OFFICE_BINDING_RECORD_SCHEMA,
    AGENTIC_DE_COMMUNICATION_EGRESS_PACKET_SCHEMA,
    AGENTIC_DE_COMMUNICATION_INGRESS_PACKET_SCHEMA,
    AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA,
    AGENTIC_DE_CONNECTOR_ADMISSION_RECORD_SCHEMA,
    AGENTIC_DE_CONNECTOR_BRIDGE_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_CONTINUATION_DECISION_RECORD_SCHEMA,
    AGENTIC_DE_CONTINUATION_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_CONTINUATION_REFRESH_DECISION_RECORD_SCHEMA,
    AGENTIC_DE_DELEGATED_WORKER_EXPORT_PACKET_SCHEMA,
    AGENTIC_DE_DELEGATED_WORKER_RECONCILIATION_REPORT_SCHEMA,
    AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
    AGENTIC_DE_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_PACKET_SCHEMA,
    AGENTIC_DE_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PACKET_SCHEMA,
    AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA,
    AGENTIC_DE_GOVERNED_COMMUNICATION_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_INGRESS_INTERPRETATION_RECORD_SCHEMA,
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
    AGENTIC_DE_MESSAGE_REWITNESS_GATE_RECORD_SCHEMA,
    AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA,
    AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA,
    AGENTIC_DE_MORPH_IR_SCHEMA,
    AGENTIC_DE_REMOTE_OPERATOR_CONTROL_BRIDGE_PACKET_SCHEMA,
    AGENTIC_DE_REMOTE_OPERATOR_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_REMOTE_OPERATOR_RESPONSE_RECORD_SCHEMA,
    AGENTIC_DE_REMOTE_OPERATOR_SESSION_RECORD_SCHEMA,
    AGENTIC_DE_REMOTE_OPERATOR_VIEW_PACKET_SCHEMA,
    AGENTIC_DE_REPO_WRITABLE_SURFACE_DESCRIPTOR_SCHEMA,
    AGENTIC_DE_REPO_WRITABLE_SURFACE_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_REPO_WRITE_LEASE_RECORD_SCHEMA,
    AGENTIC_DE_REPO_WRITE_REINTEGRATION_REPORT_SCHEMA,
    AGENTIC_DE_REPO_WRITE_RESTORATION_RECORD_SCHEMA,
    AGENTIC_DE_REPO_WRITE_SURFACE_ADMISSION_RECORD_SCHEMA,
    AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA,
    AGENTIC_DE_RUNTIME_STATE_SCHEMA,
    AGENTIC_DE_SEED_INTENT_RECORD_SCHEMA,
    AGENTIC_DE_SURFACE_AUTHORITY_DESCRIPTOR_SCHEMA,
    AGENTIC_DE_TASK_CHARTER_PACKET_SCHEMA,
    AGENTIC_DE_TASK_RESIDUAL_PACKET_SCHEMA,
    AGENTIC_DE_TASK_RESIDUAL_REFRESH_PACKET_SCHEMA,
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
    AgenticDeBridgeOfficeBindingRecord,
    AgenticDeCommunicationEgressPacket,
    AgenticDeCommunicationIngressPacket,
    AgenticDeConformanceReport,
    AgenticDeConnectorAdmissionRecord,
    AgenticDeConnectorBridgeHardeningEntry,
    AgenticDeConnectorBridgeHardeningRegister,
    AgenticDeContinuationDecisionRecord,
    AgenticDeContinuationHardeningEntry,
    AgenticDeContinuationHardeningRegister,
    AgenticDeContinuationRefreshDecisionRecord,
    AgenticDeDelegatedWorkerExportPacket,
    AgenticDeDelegatedWorkerReconciliationReport,
    AgenticDeDomainPacket,
    AgenticDeExternalAssistantEgressBridgePacket,
    AgenticDeExternalAssistantIngressBridgePacket,
    AgenticDeGovernanceCalibrationEntry,
    AgenticDeGovernanceCalibrationRegister,
    AgenticDeGovernedCommunicationHardeningEntry,
    AgenticDeGovernedCommunicationHardeningRegister,
    AgenticDeIngressInterpretationRecord,
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
    AgenticDeMessageRewitnessGateRecord,
    AgenticDeMigrationDecisionEntry,
    AgenticDeMigrationDecisionRegister,
    AgenticDeMorphDiagnosticFinding,
    AgenticDeMorphDiagnostics,
    AgenticDeMorphIr,
    AgenticDeRemoteOperatorControlBridgePacket,
    AgenticDeRemoteOperatorHardeningEntry,
    AgenticDeRemoteOperatorHardeningRegister,
    AgenticDeRemoteOperatorResponseRecord,
    AgenticDeRemoteOperatorSessionRecord,
    AgenticDeRemoteOperatorViewPacket,
    AgenticDeRepoWritableSurfaceDescriptor,
    AgenticDeRepoWritableSurfaceHardeningEntry,
    AgenticDeRepoWritableSurfaceHardeningRegister,
    AgenticDeRepoWriteLeaseRecord,
    AgenticDeRepoWriteReintegrationReport,
    AgenticDeRepoWriteRestorationRecord,
    AgenticDeRepoWriteSurfaceAdmissionRecord,
    AgenticDeRuntimeHarvestRecord,
    AgenticDeRuntimeState,
    AgenticDeSeedIntentRecord,
    AgenticDeSurfaceAuthorityDescriptor,
    AgenticDeTaskCharterPacket,
    AgenticDeTaskResidualPacket,
    AgenticDeTaskResidualRefreshPacket,
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
    ObservedWorkspaceContinuityRestorationEffect,
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
V60B_CHECKER_VERSION = "agentic_de_continuation_v60b"
V60B_TARGET_ARC = "vNext+165"
V60B_TARGET_PATH = "V60-B"
V60B_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS165.md#machine-checkable-contract"
V60C_CHECKER_VERSION = "agentic_de_continuation_v60c"
V60C_TARGET_ARC = "vNext+166"
V60C_TARGET_PATH = "V60-C"
V60C_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS166.md#machine-checkable-contract"
V61A_CHECKER_VERSION = "agentic_de_governed_communication_v61a"
V61A_TARGET_ARC = "vNext+167"
V61A_TARGET_PATH = "V61-A"
V61A_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS167.md#machine-checkable-contract"
V61A_SELECTED_API_ROUTE = "apps/api/src/adeu_api/urm_routes.py:/copilot/send"
V61A_SELECTED_RUNTIME_METHOD = "copilot.user_message"
V61A_SELECTED_SURFACE_CLASS = "resident_copilot_send_api"
V61A_SELECTED_SOURCE_PRINCIPAL_CLASS = "human_operator"
V61A_SELECTED_SPEAKER_CLASS = "resident_session_user_message"
V61B_CHECKER_VERSION = "agentic_de_governed_communication_v61b"
V61B_TARGET_ARC = "vNext+168"
V61B_TARGET_PATH = "V61-B"
V61B_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS168.md#machine-checkable-contract"
V61C_CHECKER_VERSION = "agentic_de_governed_communication_v61c"
V61C_TARGET_ARC = "vNext+169"
V61C_TARGET_PATH = "V61-C"
V61C_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS169.md#machine-checkable-contract"
V62A_CHECKER_VERSION = "agentic_de_connector_admission_v62a"
V62A_TARGET_ARC = "vNext+170"
V62A_TARGET_PATH = "V62-A"
V62A_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS170.md#machine-checkable-contract"
V62A_SELECTED_CONNECTOR_CREATE_ROUTE = "apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot"
V62A_SELECTED_CONNECTOR_GET_ROUTE = (
    "apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}"
)
V62A_SELECTED_CONNECTOR_PROVIDER = "codex"
V62A_SELECTED_CONNECTOR_PRINCIPAL = "external_assistant"
V62B_CHECKER_VERSION = "agentic_de_external_assistant_egress_bridge_v62b"
V62B_TARGET_ARC = "vNext+171"
V62B_TARGET_PATH = "V62-B"
V62B_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS171.md#machine-checkable-contract"
V62C_CHECKER_VERSION = "agentic_de_connector_bridge_hardening_v62c"
V62C_TARGET_ARC = "vNext+172"
V62C_TARGET_PATH = "V62-C"
V62C_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS172.md#machine-checkable-contract"
V63A_CHECKER_VERSION = "agentic_de_remote_operator_starter_v63a"
V63A_TARGET_ARC = "vNext+173"
V63A_TARGET_PATH = "V63-A"
V63A_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS173.md#machine-checkable-contract"
V63A_SELECTED_REMOTE_OPERATOR_PRINCIPAL = "remote_operator"
V63A_SELECTED_REMOTE_SURFACE_CLASS = "read_mostly_phone_safe_remote_operator_surface"
V63B_CHECKER_VERSION = "agentic_de_remote_operator_control_bridge_v63b"
V63B_TARGET_ARC = "vNext+174"
V63B_TARGET_PATH = "V63-B"
V63B_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS174.md#machine-checkable-contract"
V63C_CHECKER_VERSION = "agentic_de_remote_operator_hardening_v63c"
V63C_TARGET_ARC = "vNext+175"
V63C_TARGET_PATH = "V63-C"
V63C_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS175.md#machine-checkable-contract"
V64A_CHECKER_VERSION = "agentic_de_repo_writable_surface_v64a"
V64A_TARGET_ARC = "vNext+176"
V64A_TARGET_PATH = "V64-A"
V64A_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS176.md#machine-checkable-contract"
V64A_SELECTED_SURFACE_RUNTIME_SUBTREE = "runtime"
V64A_SELECTED_DESCRIPTOR_SURFACE_CLASS = "declared_subtree"
V64B_CHECKER_VERSION = "agentic_de_repo_write_restoration_v64b"
V64B_TARGET_ARC = "vNext+177"
V64B_TARGET_PATH = "V64-B"
V64B_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS177.md#machine-checkable-contract"
V64C_CHECKER_VERSION = "agentic_de_repo_writable_surface_hardening_v64c"
V64C_TARGET_ARC = "vNext+178"
V64C_TARGET_PATH = "V64-C"
V64C_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS178.md#machine-checkable-contract"
V65A_CHECKER_VERSION = "agentic_de_delegated_worker_export_v65a"
V65A_TARGET_ARC = "vNext+179"
V65A_TARGET_PATH = "V65-A"
V65A_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS179.md#machine-checkable-contract"
V65B_CHECKER_VERSION = "agentic_de_delegated_worker_reconciliation_v65b"
V65B_TARGET_ARC = "vNext+180"
V65B_TARGET_PATH = "V65-B"
V65B_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS180.md#machine-checkable-contract"


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
DEFAULT_V56B_TICKET_PATH = _default_fixture_path("v56b", "reference_agentic_de_action_ticket.json")
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
DEFAULT_V60B_LANE_DRIFT_PATH = _default_fixture_path(
    "v60b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V60B_TASK_RESIDUAL_REFRESH_PATH = _default_fixture_path(
    "v60b", "reference_agentic_de_task_residual_refresh_packet.json"
)
DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH = _default_fixture_path(
    "v60b", "reference_agentic_de_continuation_refresh_decision_record.json"
)
DEFAULT_V60C_LANE_DRIFT_PATH = _default_fixture_path(
    "v60c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V60C_HARDENING_PATH = _default_fixture_path(
    "v60c", "reference_agentic_de_continuation_hardening_register.json"
)
DEFAULT_V61A_LANE_DRIFT_PATH = _default_fixture_path(
    "v61a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V61A_SEND_REQUEST_PATH = _default_fixture_path(
    "v61a", "reference_copilot_session_send_request.json"
)
DEFAULT_V61A_COMMUNICATION_INGRESS_PATH = _default_fixture_path(
    "v61a", "reference_agentic_de_communication_ingress_packet.json"
)
DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH = _default_fixture_path(
    "v61a", "reference_agentic_de_surface_authority_descriptor.json"
)
DEFAULT_V61A_INGRESS_INTERPRETATION_PATH = _default_fixture_path(
    "v61a", "reference_agentic_de_ingress_interpretation_record.json"
)
DEFAULT_V61A_COMMUNICATION_EGRESS_PATH = _default_fixture_path(
    "v61a", "reference_agentic_de_communication_egress_packet.json"
)
DEFAULT_V61B_LANE_DRIFT_PATH = _default_fixture_path(
    "v61b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V61B_BRIDGE_OFFICE_BINDING_PATH = _default_fixture_path(
    "v61b", "reference_agentic_de_bridge_office_binding_record.json"
)
DEFAULT_V61B_MESSAGE_REWITNESS_GATE_PATH = _default_fixture_path(
    "v61b", "reference_agentic_de_message_rewitness_gate_record.json"
)
DEFAULT_V61C_LANE_DRIFT_PATH = _default_fixture_path(
    "v61c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V61C_HARDENING_PATH = _default_fixture_path(
    "v61c", "reference_agentic_de_governed_communication_hardening_register.json"
)
DEFAULT_V62A_LANE_DRIFT_PATH = _default_fixture_path(
    "v62a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V62A_CONNECTOR_SNAPSHOT_PATH = _default_fixture_path(
    "v62a", "reference_connector_snapshot_response.json"
)
DEFAULT_V62A_CONNECTOR_ADMISSION_PATH = _default_fixture_path(
    "v62a", "reference_agentic_de_connector_admission_record.json"
)
DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH = _default_fixture_path(
    "v62a", "reference_agentic_de_external_assistant_ingress_bridge_packet.json"
)
DEFAULT_V62B_LANE_DRIFT_PATH = _default_fixture_path(
    "v62b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V62B_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_PATH = _default_fixture_path(
    "v62b", "reference_agentic_de_external_assistant_egress_bridge_packet.json"
)
DEFAULT_V62C_LANE_DRIFT_PATH = _default_fixture_path(
    "v62c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V62C_CONNECTOR_BRIDGE_HARDENING_PATH = _default_fixture_path(
    "v62c", "reference_agentic_de_connector_bridge_hardening_register.json"
)
DEFAULT_V63A_LANE_DRIFT_PATH = _default_fixture_path(
    "v63a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V63A_REMOTE_OPERATOR_SESSION_PATH = _default_fixture_path(
    "v63a", "reference_agentic_de_remote_operator_session_record.json"
)
DEFAULT_V63A_REMOTE_OPERATOR_VIEW_PATH = _default_fixture_path(
    "v63a", "reference_agentic_de_remote_operator_view_packet.json"
)
DEFAULT_V63A_REMOTE_OPERATOR_RESPONSE_PATH = _default_fixture_path(
    "v63a", "reference_agentic_de_remote_operator_response_record.json"
)
DEFAULT_V63B_LANE_DRIFT_PATH = _default_fixture_path(
    "v63b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V63B_REMOTE_OPERATOR_CONTROL_BRIDGE_PATH = _default_fixture_path(
    "v63b", "reference_agentic_de_remote_operator_control_bridge_packet.json"
)
DEFAULT_V63C_LANE_DRIFT_PATH = _default_fixture_path(
    "v63c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V63C_REMOTE_OPERATOR_HARDENING_PATH = _default_fixture_path(
    "v63c", "reference_agentic_de_remote_operator_hardening_register.json"
)
DEFAULT_V64A_LANE_DRIFT_PATH = _default_fixture_path(
    "v64a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH = _default_fixture_path(
    "v64a", "reference_agentic_de_repo_writable_surface_descriptor.json"
)
DEFAULT_V64A_REPO_WRITE_LEASE_PATH = _default_fixture_path(
    "v64a", "reference_agentic_de_repo_write_lease_record.json"
)
DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH = _default_fixture_path(
    "v64a", "reference_agentic_de_repo_write_surface_admission_record.json"
)
DEFAULT_V64B_LANE_DRIFT_PATH = _default_fixture_path(
    "v64b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V64B_REPO_WRITE_RESTORATION_PATH = _default_fixture_path(
    "v64b", "reference_agentic_de_repo_write_restoration_record.json"
)
DEFAULT_V64B_REPO_WRITE_REINTEGRATION_PATH = _default_fixture_path(
    "v64b", "reference_agentic_de_repo_write_reintegration_report.json"
)
DEFAULT_V64C_LANE_DRIFT_PATH = _default_fixture_path(
    "v64c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V64C_REPO_WRITABLE_SURFACE_HARDENING_PATH = _default_fixture_path(
    "v64c", "reference_agentic_de_repo_writable_surface_hardening_register.json"
)
DEFAULT_V65A_LANE_DRIFT_PATH = _default_fixture_path(
    "v65a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V65A_DELEGATED_WORKER_EXPORT_PATH = _default_fixture_path(
    "v65a", "reference_agentic_de_delegated_worker_export_packet.json"
)
DEFAULT_V65B_LANE_DRIFT_PATH = _default_fixture_path(
    "v65b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V65B_DELEGATED_WORKER_RECONCILIATION_PATH = _default_fixture_path(
    "v65b", "reference_agentic_de_delegated_worker_reconciliation_report.json"
)
DEFAULT_V65B_WORKER_BOUNDARY_CONFORMANCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "packages"
    / "adeu_agent_harness"
    / "tests"
    / "fixtures"
    / "v48e"
    / "reference_child"
    / "worker_boundary_conformance_report.json"
)
DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH = (
    repo_root(anchor=Path(__file__))
    / "packages"
    / "adeu_agent_harness"
    / "tests"
    / "fixtures"
    / "v48e"
    / "reference_worker_delegation_topology.json"
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
DEFAULT_V60A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v164"
    / "evidence_inputs"
    / "v60a_continuation_starter_evidence_v164.json"
)
DEFAULT_V60B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v165"
    / "evidence_inputs"
    / "v60b_continuation_refresh_evidence_v165.json"
)
DEFAULT_V61A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v167"
    / "evidence_inputs"
    / "v61a_governed_communication_evidence_v167.json"
)
DEFAULT_V61B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v168"
    / "evidence_inputs"
    / "v61b_bridge_office_rewitness_evidence_v168.json"
)
DEFAULT_V61C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v169"
    / "evidence_inputs"
    / "v61c_governed_communication_hardening_evidence_v169.json"
)
DEFAULT_V62A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v170"
    / "evidence_inputs"
    / "v62a_connector_admission_evidence_v170.json"
)
DEFAULT_V62B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v171"
    / "evidence_inputs"
    / "v62b_external_assistant_egress_bridge_evidence_v171.json"
)
DEFAULT_V62C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v172"
    / "evidence_inputs"
    / "v62c_connector_bridge_hardening_evidence_v172.json"
)
DEFAULT_V63A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v173"
    / "evidence_inputs"
    / "v63a_remote_operator_starter_evidence_v173.json"
)
DEFAULT_V63B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v174"
    / "evidence_inputs"
    / "v63b_remote_operator_control_bridge_evidence_v174.json"
)
DEFAULT_V64A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v176"
    / "evidence_inputs"
    / "v64a_repo_writable_surface_starter_evidence_v176.json"
)
DEFAULT_V64B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v177"
    / "evidence_inputs"
    / "v64b_repo_write_restoration_evidence_v177.json"
)
DEFAULT_V64C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v178"
    / "evidence_inputs"
    / "v64c_repo_writable_surface_hardening_evidence_v178.json"
)
DEFAULT_V65A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v179"
    / "evidence_inputs"
    / "v65a_delegated_worker_export_starter_evidence_v179.json"
)
DEFAULT_V48D_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v115"
    / "evidence_inputs"
    / "v48d_worker_boundary_conformance_evidence_v115.json"
)
DEFAULT_V48E_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v116"
    / "evidence_inputs"
    / "v48e_worker_delegation_topology_evidence_v116.json"
)
DEFAULT_V60C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v166"
    / "evidence_inputs"
    / "v60c_continuation_hardening_evidence_v166.json"
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
EXPECTED_V60A_EVIDENCE_SCHEMA = "v60a_continuation_starter_evidence@1"
EXPECTED_V60B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS164.md"
REQUIRED_V60B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v60a_surface_reuse_default": "holds",
    "stable_loop_identity_preserved": "amended",
    "latest_reintegrated_act_selection_explicit_and_fail_closed": "amended",
    "reproposal_required_posture_only": "amended",
    "communication_law_still_deferred_to_v61": "amended",
}
EXPECTED_V60B_EVIDENCE_SCHEMA = "v60b_continuation_refresh_evidence@1"
EXPECTED_V60C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS165.md"
REQUIRED_V60C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v60a_v60b_surface_reuse_default": "holds",
    "hardening_recommendation_extensional_and_replayable": "amended",
    "explicit_frozen_policy_anchor_required": "amended",
    "path_level_non_generalization_required": "amended",
    "candidate_outcomes_non_entitling_and_non_escalating": "amended",
    "provenance_and_lineage_root_dedup_explicit": "amended",
}
EXPECTED_V61A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS166.md"
REQUIRED_V61A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v60_surface_reuse_default": "holds",
    "exact_urm_copilot_send_seam_only": "amended",
    "principal_and_speaker_typing_explicit": "amended",
    "surface_descriptor_not_message_interpretation": "amended",
    "charter_amendment_candidate_posture_only": "amended",
    "bridge_office_and_rewitness_deferred": "amended",
    "communication_egress_non_authorizing": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V61B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS167.md"
REQUIRED_V61B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v61a_surface_reuse_default": "holds",
    "bridge_office_binding_explicit_and_replayable": "amended",
    "rewitness_explicit_and_fail_closed": "amended",
    "positive_rewitness_basis_required": "amended",
    "rewitness_non_mutating_for_v60_state": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V61A_EVIDENCE_SCHEMA = "v61a_governed_communication_evidence@1"
EXPECTED_V61B_EVIDENCE_SCHEMA = "v61b_bridge_office_rewitness_evidence@1"
EXPECTED_V61C_EVIDENCE_SCHEMA = "v61c_governed_communication_hardening_evidence@1"
EXPECTED_V61C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS168.md"
REQUIRED_V61C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v61a_v61b_surface_reuse_default": "holds",
    "hardening_recommendation_extensional_and_replayable": "amended",
    "explicit_frozen_policy_anchor_required": "amended",
    "positive_rewitness_basis_carried_into_advisory_evidence": "amended",
    "path_level_non_generalization_required": "amended",
    "candidate_outcomes_non_entitling_non_escalating_and_scope_bound": "amended",
    "provenance_and_lineage_root_dedup_explicit": "amended",
}
EXPECTED_V62A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS169.md"
REQUIRED_V62A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v61_surface_reuse_default": "holds",
    "exact_connector_snapshot_path_only": "amended",
    "external_assistant_principal_only": "amended",
    "connector_admission_fail_closed_on_snapshot_exposure_freshness_basis": "amended",
    "ingress_bridge_consumes_v61a_basis_only": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V62A_EVIDENCE_SCHEMA = "v62a_connector_admission_evidence@1"
EXPECTED_V62B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS170.md"
REQUIRED_V62B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v62a_surface_reuse_default": "holds",
    "egress_bridge_only_follow_on": "amended",
    "external_assistant_principal_only": "holds",
    "explicit_v61b_basis_consumption_where_selected": "amended",
    "direct_positive_rewitness_basis_summary_required": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V62B_EVIDENCE_SCHEMA = "v62b_external_assistant_egress_bridge_evidence@1"
EXPECTED_V62C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS171.md"
REQUIRED_V62C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v62a_v62b_surface_reuse_default": "holds",
    "advisory_connector_hardening_only": "amended",
    "committed_lane_artifacts_outrank_narrative_docs": "amended",
    "explicit_frozen_policy_anchor_required": "amended",
    "positive_rewitness_basis_carry_through_fail_closed": "amended",
    "candidate_outcomes_non_entitling_non_escalating_and_scope_bound": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V62C_EVIDENCE_SCHEMA = "v62c_connector_bridge_hardening_evidence@1"
EXPECTED_V63A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS172.md"
REQUIRED_V63A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v60_v61_v62_surface_reuse_default": "holds",
    "remote_operator_principal_only": "amended",
    "read_mostly_phone_safe_view_only": "amended",
    "bounded_response_set_only": "amended",
    "selected_responses_consume_shipped_law": "amended",
    "v63b_richer_command_bridge_deferred": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V63A_EVIDENCE_SCHEMA = "v63a_remote_operator_starter_evidence@1"
EXPECTED_V63B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS173.md"
REQUIRED_V63B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v63a_surface_reuse_default": "holds",
    "richer_intervention_bridge_only": "amended",
    "explicit_v63a_view_basis_required": "amended",
    "richer_intervention_non_mutating_by_itself": "amended",
    "all_device_or_surface_generalization_forbidden": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V63B_EVIDENCE_SCHEMA = "v63b_remote_operator_control_bridge_evidence@1"
EXPECTED_V63C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS174.md"
REQUIRED_V63C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v63a_v63b_surface_reuse_default": "holds",
    "advisory_remote_hardening_only": "amended",
    "committed_lane_artifacts_outrank_narrative_docs": "amended",
    "explicit_frozen_policy_anchor_required": "amended",
    "optional_response_control_basis_fail_closed": "amended",
    "candidate_outcomes_non_entitling_non_escalating_and_scope_bound": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V60C_EVIDENCE_SCHEMA = "v60c_continuation_hardening_evidence@1"
EXPECTED_V64A_EVIDENCE_SCHEMA = "v64a_repo_writable_surface_starter_evidence@1"
EXPECTED_V64A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS175.md"
REQUIRED_V64A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v59_v60_v61_surface_reuse_default": "holds",
    "surface_widening_only_before_mutation_semantics_widening": "amended",
    "continuity_region_not_writable_entitlement": "amended",
    "communication_lineage_not_writable_entitlement": "amended",
    "canonical_membership_and_fail_closed_path_law_required": "amended",
    "per_target_admissibility_required_inside_selected_surface": "amended",
    "broader_repo_execute_dispatch_worker_authority_deferred": "amended",
}
EXPECTED_V64B_EVIDENCE_SCHEMA = "v64b_repo_write_restoration_evidence@1"
EXPECTED_V64B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS176.md"
REQUIRED_V64B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v64a_surface_reuse_default": "holds",
    "same_exact_admitted_target_reuse_default": "holds",
    "restoration_not_fresh_surface_or_lease_or_target_admission": "amended",
    "concrete_write_effect_lineage_must_remain_explicit": "amended",
    "target_membership_and_target_occupancy_carry_through_required": "amended",
    "preserved_local_write_create_new_semantics_only": "amended",
    "broader_repo_execute_dispatch_worker_authority_deferred": "amended",
}
EXPECTED_V64C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS177.md"
REQUIRED_V64C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v64a_v64b_surface_reuse_default": "holds",
    "advisory_writable_surface_hardening_only": "amended",
    "committed_lane_artifacts_outrank_narrative_docs": "amended",
    "explicit_frozen_policy_anchor_required": "amended",
    "optional_restoration_reintegration_basis_fail_closed": "amended",
    "candidate_outcomes_non_entitling_non_escalating_and_scope_bound": "amended",
    "path_level_non_generalization_required": "amended",
}
EXPECTED_V64C_EVIDENCE_SCHEMA = "v64c_repo_writable_surface_hardening_evidence@1"
EXPECTED_V65A_EVIDENCE_SCHEMA = "v65a_delegated_worker_export_starter_evidence@1"
EXPECTED_V48D_EVIDENCE_SCHEMA = "v48d_worker_boundary_conformance_evidence@1"
EXPECTED_V48E_EVIDENCE_SCHEMA = "v48e_worker_delegation_topology_evidence@1"
EXPECTED_V65A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS178.md"
REQUIRED_V65A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v64_v48_surface_reuse_default": "holds",
    "export_bridge_only_before_reconciliation_or_dispatch_widening": "amended",
    "v64c_advisory_hardening_context_only_not_export_entitlement": "amended",
    "explicit_worker_carrier_and_single_topology_basis_required": "amended",
    "explicit_v60_v61_replayability_inputs_required": "amended",
    "preserved_local_write_create_new_semantics_only": "amended",
    "broader_dispatch_execute_multi_worker_connector_remote_authority_deferred": "amended",
}
EXPECTED_V65B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS179.md"
REQUIRED_V65B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v65a_export_reuse_default": "holds",
    "same_exported_scope_and_topology_reuse_default": "holds",
    "released_worker_result_or_conformance_basis_must_be_explicit": "amended",
    "worker_result_basis_must_match_carrier_topology_and_exported_scope": "amended",
    "preserved_local_write_create_new_semantics_only": "amended",
    "reconciliation_not_fresh_local_or_export_or_topology_selection": "amended",
    "broader_dispatch_execute_multi_worker_connector_remote_authority_deferred": "amended",
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
            f"unexpected schema marker for live-turn admission record: {payload.schema}"
        )
    return payload


def load_live_turn_handoff_record(path: Path) -> AgenticDeLiveTurnHandoffRecord:
    payload = AgenticDeLiveTurnHandoffRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_TURN_HANDOFF_RECORD_SCHEMA:
        raise ValueError(f"unexpected schema marker for live-turn handoff record: {payload.schema}")
    return payload


def load_live_turn_reintegration_report(path: Path) -> AgenticDeLiveTurnReintegrationReport:
    payload = AgenticDeLiveTurnReintegrationReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_TURN_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for live-turn reintegration report: {payload.schema}"
        )
    return payload


def load_workspace_continuity_region_declaration(
    path: Path,
) -> AgenticDeWorkspaceContinuityRegionDeclaration:
    payload = AgenticDeWorkspaceContinuityRegionDeclaration.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_REGION_DECLARATION_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity region declaration: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_continuity_admission_record(
    path: Path,
) -> AgenticDeWorkspaceContinuityAdmissionRecord:
    payload = AgenticDeWorkspaceContinuityAdmissionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_ADMISSION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for workspace continuity admission record: {payload.schema}"
        )
    return payload


def load_workspace_occupancy_report(path: Path) -> AgenticDeWorkspaceOccupancyReport:
    payload = AgenticDeWorkspaceOccupancyReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_WORKSPACE_OCCUPANCY_REPORT_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for workspace occupancy report: {payload.schema}"
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
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_RESTORATION_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity restoration reintegration "
            f"report: {payload.schema}"
        )
    return payload


def load_workspace_continuity_hardening_register(
    path: Path,
) -> AgenticDeWorkspaceContinuityHardeningRegister:
    payload = AgenticDeWorkspaceContinuityHardeningRegister.model_validate(_read_json_object(path))
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


def load_task_residual_refresh_packet(path: Path) -> AgenticDeTaskResidualRefreshPacket:
    payload = AgenticDeTaskResidualRefreshPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_TASK_RESIDUAL_REFRESH_PACKET_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for task residual refresh packet: {payload.schema}"
        )
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
            f"unexpected schema marker for continuation decision record: {payload.schema}"
        )
    return payload


def load_continuation_refresh_decision_record(
    path: Path,
) -> AgenticDeContinuationRefreshDecisionRecord:
    payload = AgenticDeContinuationRefreshDecisionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_CONTINUATION_REFRESH_DECISION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for continuation refresh decision record: {payload.schema}"
        )
    return payload


def load_continuation_hardening_register(
    path: Path,
) -> AgenticDeContinuationHardeningRegister:
    payload = AgenticDeContinuationHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_CONTINUATION_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for continuation hardening register: {payload.schema}"
        )
    return payload


def load_communication_ingress_packet(path: Path) -> AgenticDeCommunicationIngressPacket:
    payload = AgenticDeCommunicationIngressPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_COMMUNICATION_INGRESS_PACKET_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for communication ingress packet: {payload.schema}"
        )
    return payload


def load_surface_authority_descriptor(path: Path) -> AgenticDeSurfaceAuthorityDescriptor:
    payload = AgenticDeSurfaceAuthorityDescriptor.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_SURFACE_AUTHORITY_DESCRIPTOR_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for surface authority descriptor: {payload.schema}"
        )
    return payload


def load_ingress_interpretation_record(path: Path) -> AgenticDeIngressInterpretationRecord:
    payload = AgenticDeIngressInterpretationRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_INGRESS_INTERPRETATION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for ingress interpretation record: {payload.schema}"
        )
    return payload


def load_communication_egress_packet(path: Path) -> AgenticDeCommunicationEgressPacket:
    payload = AgenticDeCommunicationEgressPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_COMMUNICATION_EGRESS_PACKET_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for communication egress packet: {payload.schema}"
        )
    return payload


def load_bridge_office_binding_record(path: Path) -> AgenticDeBridgeOfficeBindingRecord:
    payload = AgenticDeBridgeOfficeBindingRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_BRIDGE_OFFICE_BINDING_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for bridge-office binding record: {payload.schema}"
        )
    return payload


def load_message_rewitness_gate_record(path: Path) -> AgenticDeMessageRewitnessGateRecord:
    payload = AgenticDeMessageRewitnessGateRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_MESSAGE_REWITNESS_GATE_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for message rewitness gate record: {payload.schema}"
        )
    return payload


def load_governed_communication_hardening_register(
    path: Path,
) -> AgenticDeGovernedCommunicationHardeningRegister:
    payload = AgenticDeGovernedCommunicationHardeningRegister.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_GOVERNED_COMMUNICATION_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            "unexpected schema marker for governed communication hardening register: "
            f"{payload.schema}"
        )
    return payload


def load_connector_bridge_hardening_register(
    path: Path,
) -> AgenticDeConnectorBridgeHardeningRegister:
    payload = AgenticDeConnectorBridgeHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_CONNECTOR_BRIDGE_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for connector bridge hardening register: {payload.schema}"
        )
    return payload


def load_remote_operator_session_record(path: Path) -> AgenticDeRemoteOperatorSessionRecord:
    payload = AgenticDeRemoteOperatorSessionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REMOTE_OPERATOR_SESSION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for remote operator session record: {payload.schema}"
        )
    return payload


def load_remote_operator_view_packet(path: Path) -> AgenticDeRemoteOperatorViewPacket:
    payload = AgenticDeRemoteOperatorViewPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REMOTE_OPERATOR_VIEW_PACKET_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for remote operator view packet: {payload.schema}"
        )
    return payload


def load_remote_operator_response_record(path: Path) -> AgenticDeRemoteOperatorResponseRecord:
    payload = AgenticDeRemoteOperatorResponseRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REMOTE_OPERATOR_RESPONSE_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for remote operator response record: {payload.schema}"
        )
    return payload


def load_remote_operator_control_bridge_packet(
    path: Path,
) -> AgenticDeRemoteOperatorControlBridgePacket:
    payload = AgenticDeRemoteOperatorControlBridgePacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REMOTE_OPERATOR_CONTROL_BRIDGE_PACKET_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for remote operator control bridge packet: {payload.schema}"
        )
    return payload


def load_remote_operator_hardening_register(
    path: Path,
) -> AgenticDeRemoteOperatorHardeningRegister:
    payload = AgenticDeRemoteOperatorHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REMOTE_OPERATOR_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for remote operator hardening register: {payload.schema}"
        )
    return payload


def load_repo_writable_surface_descriptor(path: Path) -> AgenticDeRepoWritableSurfaceDescriptor:
    payload = AgenticDeRepoWritableSurfaceDescriptor.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REPO_WRITABLE_SURFACE_DESCRIPTOR_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for repo writable surface descriptor: {payload.schema}"
        )
    return payload


def load_repo_write_lease_record(path: Path) -> AgenticDeRepoWriteLeaseRecord:
    payload = AgenticDeRepoWriteLeaseRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REPO_WRITE_LEASE_RECORD_SCHEMA:
        raise ValueError(f"unexpected schema marker for repo write lease record: {payload.schema}")
    return payload


def load_repo_write_surface_admission_record(
    path: Path,
) -> AgenticDeRepoWriteSurfaceAdmissionRecord:
    payload = AgenticDeRepoWriteSurfaceAdmissionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REPO_WRITE_SURFACE_ADMISSION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for repo write surface admission record: {payload.schema}"
        )
    return payload


def load_repo_write_restoration_record(path: Path) -> AgenticDeRepoWriteRestorationRecord:
    payload = AgenticDeRepoWriteRestorationRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REPO_WRITE_RESTORATION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for repo write restoration record: {payload.schema}"
        )
    return payload


def load_repo_write_reintegration_report(path: Path) -> AgenticDeRepoWriteReintegrationReport:
    payload = AgenticDeRepoWriteReintegrationReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REPO_WRITE_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for repo write reintegration report: "
            f"{payload.schema}"
        )
    return payload


def load_repo_writable_surface_hardening_register(
    path: Path,
) -> AgenticDeRepoWritableSurfaceHardeningRegister:
    payload = AgenticDeRepoWritableSurfaceHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_REPO_WRITABLE_SURFACE_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            "unexpected schema marker for repo writable surface hardening register: "
            f"{payload.schema}"
        )
    return payload


def load_delegated_worker_export_packet(path: Path) -> AgenticDeDelegatedWorkerExportPacket:
    payload = AgenticDeDelegatedWorkerExportPacket.model_validate(
        _load_json_object(path, error_label="delegated worker export packet")
    )
    if payload.schema != AGENTIC_DE_DELEGATED_WORKER_EXPORT_PACKET_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for delegated worker export packet: {payload.schema}"
        )
    return payload


def load_delegated_worker_reconciliation_report(
    path: Path,
) -> AgenticDeDelegatedWorkerReconciliationReport:
    payload = AgenticDeDelegatedWorkerReconciliationReport.model_validate(
        _load_json_object(path, error_label="delegated worker reconciliation report")
    )
    if payload.schema != AGENTIC_DE_DELEGATED_WORKER_RECONCILIATION_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for delegated worker reconciliation report: "
            f"{payload.schema}"
        )
    return payload


def load_worker_boundary_conformance_report(path: Path) -> WorkerBoundaryConformanceReport:
    payload = WorkerBoundaryConformanceReport.model_validate(
        _load_json_object(path, error_label="worker boundary conformance report")
    )
    if payload.schema != WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for worker boundary conformance report: {payload.schema}"
        )
    return payload


def load_worker_delegation_topology(path: Path) -> WorkerDelegationTopology:
    payload = WorkerDelegationTopology.model_validate(
        _load_json_object(path, error_label="worker delegation topology")
    )
    if payload.schema != WORKER_DELEGATION_TOPOLOGY_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for worker delegation topology: {payload.schema}"
        )
    return payload


def load_connector_snapshot_response(path: Path) -> ConnectorSnapshotResponse:
    return ConnectorSnapshotResponse.model_validate(
        _load_json_object(path, error_label="connector snapshot")
    )


def load_connector_admission_record(path: Path) -> AgenticDeConnectorAdmissionRecord:
    payload = AgenticDeConnectorAdmissionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_CONNECTOR_ADMISSION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for connector admission record: {payload.schema}"
        )
    return payload


def load_external_assistant_ingress_bridge_packet(
    path: Path,
) -> AgenticDeExternalAssistantIngressBridgePacket:
    payload = AgenticDeExternalAssistantIngressBridgePacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PACKET_SCHEMA:
        raise ValueError(
            "unexpected schema marker for external assistant ingress bridge packet: "
            f"{payload.schema}"
        )
    return payload


def load_external_assistant_egress_bridge_packet(
    path: Path,
) -> AgenticDeExternalAssistantEgressBridgePacket:
    payload = AgenticDeExternalAssistantEgressBridgePacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_PACKET_SCHEMA:
        raise ValueError(
            "unexpected schema marker for external assistant egress bridge packet: "
            f"{payload.schema}"
        )
    return payload


def load_copilot_session_send_request(path: Path) -> CopilotSessionSendRequest:
    payload = _load_json_object(path, error_label="copilot session send request")
    return CopilotSessionSendRequest.model_validate(payload)


def load_live_restoration_handoff_record(path: Path) -> AgenticDeLiveRestorationHandoffRecord:
    payload = AgenticDeLiveRestorationHandoffRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_RESTORATION_HANDOFF_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for live restoration handoff record: {payload.schema}"
        )
    return payload


def load_live_restoration_reintegration_report(
    path: Path,
) -> AgenticDeLiveRestorationReintegrationReport:
    payload = AgenticDeLiveRestorationReintegrationReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_RESTORATION_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for live restoration reintegration report: {payload.schema}"
        )
    return payload


def load_live_harness_hardening_register(
    path: Path,
) -> AgenticDeLiveHarnessHardeningRegister:
    payload = AgenticDeLiveHarnessHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_HARNESS_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for live harness hardening register: {payload.schema}"
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
            f"unexpected schema marker for governance calibration register: {payload.schema}"
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
            f"unexpected schema marker for local-effect observation record: {payload.schema}"
        )
    return payload


def load_local_effect_conformance_report(path: Path) -> AgenticDeLocalEffectConformanceReport:
    payload = AgenticDeLocalEffectConformanceReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_CONFORMANCE_REPORT_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for local-effect conformance report: {payload.schema}"
        )
    return payload


def load_local_effect_restoration_record(path: Path) -> AgenticDeLocalEffectRestorationRecord:
    payload = AgenticDeLocalEffectRestorationRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_RESTORATION_RECORD_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for local-effect restoration record: {payload.schema}"
        )
    return payload


def load_local_effect_hardening_register(path: Path) -> AgenticDeLocalEffectHardeningRegister:
    payload = AgenticDeLocalEffectHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for local-effect hardening register: {payload.schema}"
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


def _assert_v60a_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V60-A continuation")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.exists() and current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components for V60-A continuation"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path.resolve())
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V60-A continuation"
        ) from exc


def _assert_v60b_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V60-B continuation")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components for V60-B continuation"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path.resolve())
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V60-B continuation"
        ) from exc


def _assert_v60c_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components for V60-C continuation"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V60-C continuation"
        ) from exc


def _assert_v61a_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V61-A communication")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components for V61-A communication"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path.resolve())
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V61-A communication"
        ) from exc


def _assert_v61b_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V61-B communication")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components for V61-B communication"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V61-B communication"
        ) from exc


def _assert_v61c_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V61-C communication")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components for V61-C communication"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V61-C communication"
        ) from exc


def _assert_v62a_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V62-A connector admission")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError:
        relative = None
    if relative is not None:
        current = repo_root_path
        for part in relative.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(
                    f"{field_name} may not traverse symlink components "
                    "for V62-A connector admission"
                )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path.resolve())
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V62-A connector admission"
        ) from exc


def _assert_v62b_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V62-B external assistant bridge")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V62-B "
            "external assistant bridge"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components "
                "for V62-B external assistant bridge"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V62-B external "
            "assistant bridge"
        ) from exc


def _assert_v62c_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V62-C connector hardening")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V62-C "
            "connector hardening"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V62-C connector hardening"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V62-C connector hardening"
        ) from exc


def _assert_v63a_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V63-A remote operator starter")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V63-A "
            "remote operator starter"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V63-A remote operator "
                "starter"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V63-A remote operator starter"
        ) from exc


def _assert_v63b_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V63-B remote operator control bridge"
        )
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V63-B "
            "remote operator control bridge"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V63-B remote operator "
                "control bridge"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V63-B remote operator "
            "control bridge"
        ) from exc


def _assert_v63c_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V63-C remote hardening")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V63-C remote hardening"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V63-C remote hardening"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V63-C remote hardening"
        ) from exc


def _assert_v64a_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V64-A writable surface")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V64-A writable surface"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V64-A writable surface"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V64-A writable surface"
        ) from exc


def _assert_v64b_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError("repository root may not be a symlink for V64-B repo restoration")
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V64-B repo restoration"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V64-B repo restoration"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V64-B repo restoration"
        ) from exc


def _assert_v64c_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V64-C repo writable surface hardening"
        )
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V64-C repo "
            "writable surface hardening"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V64-C repo writable "
                "surface hardening"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V64-C repo writable "
            "surface hardening"
        ) from exc


def _assert_v65a_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V65-A delegated worker export"
        )
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V65-A delegated "
            "worker export"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V65-A delegated worker "
                "export"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V65-A delegated worker "
            "export"
        ) from exc


def _assert_v65b_repo_local_input_path(
    *,
    repo_root_path: Path,
    candidate: Path,
    field_name: str,
) -> None:
    if repo_root_path.exists() and repo_root_path.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V65-B delegated worker reconciliation"
        )
    try:
        relative = candidate.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must be lexically within the repository root for V65-B delegated "
            "worker reconciliation"
        ) from exc
    current = repo_root_path
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(
                f"{field_name} may not traverse symlink components for V65-B delegated worker "
                "reconciliation"
            )
    candidate_resolved = candidate.resolve(strict=False)
    try:
        candidate_resolved.relative_to(repo_root_path)
    except ValueError as exc:
        raise ValueError(
            f"{field_name} must remain within the repository root for V65-B delegated worker "
            "reconciliation"
        ) from exc


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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
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


def _validate_v60b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V60B_TARGET_ARC:
        raise ValueError(
            f"V60-B lane drift record must target {V60B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V60B_TARGET_PATH:
        raise ValueError(
            f"V60-B lane drift record must target {V60B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V60B_PRIOR_LANE_REF:
        raise ValueError(
            "V60-B lane drift record must point at "
            f"{EXPECTED_V60B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V60B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V60B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V60-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v60c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V60C_TARGET_ARC:
        raise ValueError(
            f"V60-C lane drift record must target {V60C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V60C_TARGET_PATH:
        raise ValueError(
            f"V60-C lane drift record must target {V60C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V60C_PRIOR_LANE_REF:
        raise ValueError(
            "V60-C lane drift record must point at "
            f"{EXPECTED_V60C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V60C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V60C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V60-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v61a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V61A_TARGET_ARC:
        raise ValueError(
            f"V61-A lane drift record must target {V61A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V61A_TARGET_PATH:
        raise ValueError(
            f"V61-A lane drift record must target {V61A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V61A_PRIOR_LANE_REF:
        raise ValueError(
            "V61-A lane drift record must point at "
            f"{EXPECTED_V61A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V61A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V61A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V61-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v61b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V61B_TARGET_ARC:
        raise ValueError(
            f"V61-B lane drift record must target {V61B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V61B_TARGET_PATH:
        raise ValueError(
            f"V61-B lane drift record must target {V61B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V61B_PRIOR_LANE_REF:
        raise ValueError(
            "V61-B lane drift record must point at "
            f"{EXPECTED_V61B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V61B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V61B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V61-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v61c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V61C_TARGET_ARC:
        raise ValueError(
            f"V61-C lane drift record must target {V61C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V61C_TARGET_PATH:
        raise ValueError(
            f"V61-C lane drift record must target {V61C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V61C_PRIOR_LANE_REF:
        raise ValueError(
            "V61-C lane drift record must point at "
            f"{EXPECTED_V61C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V61C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V61C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V61-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v62a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V62A_TARGET_ARC:
        raise ValueError(
            f"V62-A lane drift record must target {V62A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V62A_TARGET_PATH:
        raise ValueError(
            f"V62-A lane drift record must target {V62A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V62A_PRIOR_LANE_REF:
        raise ValueError(
            "V62-A lane drift record must point at "
            f"{EXPECTED_V62A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V62A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V62A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V62-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v62b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V62B_TARGET_ARC:
        raise ValueError(
            f"V62-B lane drift record must target {V62B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V62B_TARGET_PATH:
        raise ValueError(
            f"V62-B lane drift record must target {V62B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V62B_PRIOR_LANE_REF:
        raise ValueError(
            "V62-B lane drift record must point at "
            f"{EXPECTED_V62B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V62B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V62B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V62-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v62c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V62C_TARGET_ARC:
        raise ValueError(
            f"V62-C lane drift record must target {V62C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V62C_TARGET_PATH:
        raise ValueError(
            f"V62-C lane drift record must target {V62C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V62C_PRIOR_LANE_REF:
        raise ValueError(
            "V62-C lane drift record must point at "
            f"{EXPECTED_V62C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V62C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V62C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V62-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v63a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V63A_TARGET_ARC:
        raise ValueError(
            f"V63-A lane drift record must target {V63A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V63A_TARGET_PATH:
        raise ValueError(
            f"V63-A lane drift record must target {V63A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V63A_PRIOR_LANE_REF:
        raise ValueError(
            "V63-A lane drift record must point at "
            f"{EXPECTED_V63A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V63A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V63A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V63-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v63b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V63B_TARGET_ARC:
        raise ValueError(
            f"V63-B lane drift record must target {V63B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V63B_TARGET_PATH:
        raise ValueError(
            f"V63-B lane drift record must target {V63B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V63B_PRIOR_LANE_REF:
        raise ValueError(
            "V63-B lane drift record must point at "
            f"{EXPECTED_V63B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V63B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V63B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V63-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v63c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V63C_TARGET_ARC:
        raise ValueError(
            f"V63-C lane drift record must target {V63C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V63C_TARGET_PATH:
        raise ValueError(
            f"V63-C lane drift record must target {V63C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V63C_PRIOR_LANE_REF:
        raise ValueError(
            "V63-C lane drift record must point at "
            f"{EXPECTED_V63C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V63C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V63C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V63-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v64a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V64A_TARGET_ARC:
        raise ValueError(
            f"V64-A lane drift record must target {V64A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V64A_TARGET_PATH:
        raise ValueError(
            f"V64-A lane drift record must target {V64A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V64A_PRIOR_LANE_REF:
        raise ValueError(
            "V64-A lane drift record must point at "
            f"{EXPECTED_V64A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V64A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V64A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V64-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v64b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V64B_TARGET_ARC:
        raise ValueError(
            f"V64-B lane drift record must target {V64B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V64B_TARGET_PATH:
        raise ValueError(
            f"V64-B lane drift record must target {V64B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V64B_PRIOR_LANE_REF:
        raise ValueError(
            "V64-B lane drift record must point at "
            f"{EXPECTED_V64B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V64B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V64B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V64-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v64c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V64C_TARGET_ARC:
        raise ValueError(
            f"V64-C lane drift record must target {V64C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V64C_TARGET_PATH:
        raise ValueError(
            f"V64-C lane drift record must target {V64C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V64C_PRIOR_LANE_REF:
        raise ValueError(
            "V64-C lane drift record must point at "
            f"{EXPECTED_V64C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V64C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V64C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V64-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v65a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V65A_TARGET_ARC:
        raise ValueError(
            f"V65-A lane drift record must target {V65A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V65A_TARGET_PATH:
        raise ValueError(
            f"V65-A lane drift record must target {V65A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V65A_PRIOR_LANE_REF:
        raise ValueError(
            "V65-A lane drift record must point at "
            f"{EXPECTED_V65A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V65A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V65A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V65-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v65b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V65B_TARGET_ARC:
        raise ValueError(
            f"V65-B lane drift record must target {V65B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V65B_TARGET_PATH:
        raise ValueError(
            f"V65-B lane drift record must target {V65B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V65B_PRIOR_LANE_REF:
        raise ValueError(
            "V65-B lane drift record must point at "
            f"{EXPECTED_V65B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V65B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V65B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V65-B lane drift record does not satisfy the required handoff posture; "
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
            "V56-B evidence must preserve explicit ticket visibility in the consequence chain"
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
        raise ValueError("V57-B evidence must preserve non-promoting restoration record semantics")
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
        raise ValueError("V58-A evidence must preserve witness-bearing positive reintegration")
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


def _validate_v60a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V60A_EVIDENCE_SCHEMA:
        raise ValueError("V60-B requires the shipped V60-A continuation evidence payload on main")
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_seed_intent_record@1",
        "agentic_de_task_charter_packet@1",
        "agentic_de_task_residual_packet@1",
        "agentic_de_loop_state_ledger@1",
        "agentic_de_continuation_decision_record@1",
    } - set(selected_shapes):
        raise ValueError("V60-A evidence must preserve the shipped continuation starter surfaces")
    required_true_fields = (
        "task_charter_compilation_typed_and_replayable",
        "continuation_decision_typed_and_replayable",
        "continue_to_governed_act_requires_exact_selected_downstream_path",
        "emit_governed_communication_posture_only_until_v61",
        "starter_seed_ingress_not_raw_transcript_semantics",
        "starter_seed_ingress_not_generic_chat_memory",
        "starter_seed_ingress_not_connector_traffic",
        "admitted_shaping_input_set_closed_for_v60a",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V60-A evidence must preserve {field_name}")
    if payload.get("selected_live_session_surface_for_v60a") != "urm_copilot_session_path_only":
        raise ValueError("V60-A evidence must preserve the URM copilot session path only")
    if payload.get("selected_downstream_action_class_for_v60a") != "local_write":
        raise ValueError("V60-A evidence must preserve the local_write-only downstream class")
    if payload.get("selected_downstream_write_kind_for_v60a") != "create_new":
        raise ValueError("V60-A evidence must preserve the create_new-only downstream write kind")
    if payload.get("selected_continuity_root_for_v60a") != (
        DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix() + "/"
    ):
        raise ValueError("V60-A evidence must preserve the selected continuity root")
    if payload.get("v56_ticket_duration_mode_preserved") != "single_step_local":
        raise ValueError("V60-A evidence must preserve single_step_local ticket duration")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V60-A evidence must preserve non-live continuation posture")
    return payload


def _validate_v60b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V60B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V60-C requires the shipped V60-B continuation refresh evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_task_residual_refresh_packet@1",
        "agentic_de_continuation_refresh_decision_record@1",
    } - set(selected_shapes):
        raise ValueError("V60-B evidence must preserve the shipped continuation refresh surfaces")
    required_true_fields = (
        "stable_loop_identity_preserved",
        "latest_reintegrated_act_selection_explicit_and_fail_closed",
        "reproposal_required_posture_only_until_later_family",
        "reproposal_required_not_implicit_charter_amendment_or_seed_ingress",
        "emit_governed_communication_posture_only_until_v61",
        "admitted_shaping_input_set_closed_for_v60b",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V60-B evidence must preserve {field_name}")
    if payload.get("selected_live_session_surface_for_v60b") != "urm_copilot_session_path_only":
        raise ValueError("V60-B evidence must preserve the URM copilot session path only")
    if payload.get("selected_downstream_action_class_for_v60b") != "local_write":
        raise ValueError("V60-B evidence must preserve the local_write-only downstream class")
    if payload.get("selected_downstream_write_kind_for_v60b") != "create_new":
        raise ValueError("V60-B evidence must preserve the create_new-only downstream write kind")
    if payload.get("selected_continuity_root_for_v60b") != (
        DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix() + "/"
    ):
        raise ValueError("V60-B evidence must preserve the selected continuity root")
    if payload.get("v56_ticket_duration_mode_preserved") != "single_step_local":
        raise ValueError("V60-B evidence must preserve single_step_local ticket duration")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V60-B evidence must preserve non-live refresh posture")
    return payload


def _validate_v60c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V60C_EVIDENCE_SCHEMA:
        raise ValueError(
            "V64-A requires the shipped V60-C continuation hardening evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or (
        "agentic_de_continuation_hardening_register@1" not in selected_shapes
    ):
        raise ValueError("V60-C evidence must preserve the shipped hardening register shape")
    required_true_fields = (
        "advisory_only",
        "candidate_only",
        "explicit_frozen_policy_anchor_required",
        "recommendation_function_extensional_and_replayable",
        "lineage_root_non_independence_dedup_applied",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V60-C evidence must preserve {field_name}")
    if payload.get("selected_live_session_surface_for_v60c") != "urm_copilot_session_path_only":
        raise ValueError("V60-C evidence must preserve the URM copilot session path only")
    if payload.get("selected_downstream_action_class_for_v60c") != "local_write":
        raise ValueError("V60-C evidence must preserve the local_write-only downstream class")
    if payload.get("selected_downstream_write_kind_for_v60c") != "create_new":
        raise ValueError("V60-C evidence must preserve the create_new-only downstream write kind")
    if payload.get("selected_continuity_root_for_v60c") != (
        DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix() + "/"
    ):
        raise ValueError("V60-C evidence must preserve the selected continuity root")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V60-C evidence must preserve non-live advisory posture")
    return payload


def _validate_v61a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V61A_EVIDENCE_SCHEMA:
        raise ValueError(
            "V61-B requires the shipped V61-A governed communication evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_communication_ingress_packet@1",
        "agentic_de_surface_authority_descriptor@1",
        "agentic_de_ingress_interpretation_record@1",
        "agentic_de_communication_egress_packet@1",
    } - set(selected_shapes):
        raise ValueError("V61-A evidence must preserve the shipped governed communication surfaces")
    required_true_fields = (
        "communication_ingress_must_be_typed_and_replayable",
        "surface_authority_descriptor_must_be_typed_and_replayable",
        "ingress_interpretation_must_be_typed_and_replayable",
        "communication_egress_must_be_typed_and_replayable",
        "charter_amendment_candidate_posture_only_in_v61a",
        "egress_posture_only_in_v61a",
        "egress_not_native_witness_by_default",
        "path_level_non_generalization_required_for_v61a",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V61-A evidence must preserve {field_name}")
    if payload.get("selected_resident_send_surface_for_v61a") != "urm_copilot_send_path_only":
        raise ValueError("V61-A evidence must preserve the resident send seam only")
    if payload.get("selected_runtime_message_method_for_v61a") != (
        f"{V61A_SELECTED_RUNTIME_METHOD}_only"
    ):
        raise ValueError("V61-A evidence must preserve copilot.user_message only")
    if payload.get("bridge_office_binding_selected_for_v61a") is not False:
        raise ValueError("V61-A evidence must preserve bridge-office deferral")
    if payload.get("rewitness_message_promotion_selected_for_v61a") is not False:
        raise ValueError("V61-A evidence must preserve rewitness deferral")
    return payload


def _validate_v61b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V61B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V61-C requires the shipped V61-B bridge office / rewitness evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_bridge_office_binding_record@1",
        "agentic_de_message_rewitness_gate_record@1",
    } - set(selected_shapes):
        raise ValueError("V61-B evidence must preserve the shipped bridge / rewitness surfaces")
    required_true_fields = (
        "bridge_office_binding_must_be_typed_and_replayable",
        "message_rewitness_gate_must_be_typed_and_replayable",
        "communication_access_not_bridge_office",
        "positive_rewitness_requires_witness_basis_ref_or_certificate_ref",
        "missing_positive_rewitness_basis_fails_closed",
        "positive_rewitness_not_charter_mutation",
        "positive_rewitness_not_residual_mutation",
        "positive_rewitness_not_loop_state_mutation",
        "positive_rewitness_not_continuation_decision_mutation",
        "path_level_non_generalization_required_for_v61b",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V61-B evidence must preserve {field_name}")
    if payload.get("selected_resident_send_surface_for_v61b") != "urm_copilot_send_path_only":
        raise ValueError("V61-B evidence must preserve the resident send seam only")
    if payload.get("selected_runtime_message_method_for_v61b") != (
        f"{V61A_SELECTED_RUNTIME_METHOD}_only"
    ):
        raise ValueError("V61-B evidence must preserve copilot.user_message only")
    if payload.get("selected_downstream_action_class_for_v61b") != "local_write":
        raise ValueError("V61-B evidence must preserve the local_write-only downstream class")
    if payload.get("selected_downstream_write_kind_for_v61b") != "create_new":
        raise ValueError("V61-B evidence must preserve the create_new-only downstream write kind")
    return payload


def _validate_v61c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V61C_EVIDENCE_SCHEMA:
        raise ValueError(
            "V62-A requires the shipped V61-C governed communication hardening evidence "
            "payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or (
        "agentic_de_governed_communication_hardening_register@1" not in selected_shapes
    ):
        raise ValueError("V61-C evidence must preserve the shipped hardening register surface")
    required_true_fields = (
        "governed_communication_hardening_register_must_be_typed_and_replayable",
        "recommendation_function_extensional_and_replayable",
        "evidence_basis_distinct_from_recommendation",
        "explicit_frozen_policy_anchor_required",
        "lineage_root_non_independence_dedup_applied",
        "positive_rewitness_basis_explicitly_carried_when_present",
        "latest_continuation_basis_selection_explicit",
        "path_level_non_generalization_required_for_v61c",
        "advisory_only",
        "candidate_only",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V61-C evidence must preserve {field_name}")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V61-C evidence must keep hardening outputs non-live by default")
    if payload.get("selected_resident_send_surface_for_v61c") != "urm_copilot_send_path_only":
        raise ValueError("V61-C evidence must preserve the resident send seam only")
    if payload.get("selected_runtime_message_method_for_v61c") != (
        f"{V61A_SELECTED_RUNTIME_METHOD}_only"
    ):
        raise ValueError("V61-C evidence must preserve copilot.user_message only")
    if payload.get("connector_transport_law_selected_for_v61c") is not False:
        raise ValueError("V61-C evidence must preserve connector transport deferral")
    return payload


def _validate_v62a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V62A_EVIDENCE_SCHEMA:
        raise ValueError(
            "V62-B requires the shipped V62-A connector admission evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_connector_admission_record@1",
        "agentic_de_external_assistant_ingress_bridge_packet@1",
    } - set(selected_shapes):
        raise ValueError("V62-A evidence must preserve the shipped admission and ingress shapes")
    required_true_fields = (
        "connector_admission_must_be_typed_and_replayable",
        "external_assistant_ingress_bridge_must_be_typed_and_replayable",
        "ingress_bridge_consumes_v61a_basis_only_in_v62a",
        "v61b_bridge_office_or_rewitness_basis_not_selected_for_v62a_ingress",
        "path_level_non_generalization_required_for_v62a",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V62-A evidence must preserve {field_name}")
    if payload.get("selected_connector_provider_for_v62a") != "codex_only":
        raise ValueError("V62-A evidence must preserve the codex connector provider only")
    if payload.get("selected_connector_principal_for_v62a") != "external_assistant_only":
        raise ValueError("V62-A evidence must preserve the external_assistant principal only")
    if payload.get("connector_egress_bridge_selected_for_v62a") is not False:
        raise ValueError("V62-A evidence must preserve egress-bridge deferral")
    if payload.get("human_via_connector_selected_for_v62a") is not False:
        raise ValueError("V62-A evidence must preserve human-via-connector deferral")
    return payload


def _validate_v62b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V62B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V62-C requires the shipped V62-B external assistant egress bridge evidence "
            "payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_external_assistant_egress_bridge_packet@1"
    } - set(selected_shapes):
        raise ValueError("V62-B evidence must preserve the shipped egress bridge shape")
    required_true_fields = (
        "external_assistant_egress_bridge_must_be_typed_and_replayable",
        "egress_bridge_consumes_shipped_v62a_basis",
        "egress_bridge_consumes_shipped_v61a_egress_basis",
        "egress_bridge_consumes_shipped_v61b_basis_where_selected",
        "missing_positive_rewitness_basis_fails_closed_in_v62b",
        "path_level_non_generalization_required_for_v62b",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V62-B evidence must preserve {field_name}")
    if payload.get("selected_connector_provider_for_v62_basis") != "codex_only":
        raise ValueError("V62-B evidence must preserve the codex connector provider only")
    if payload.get("selected_connector_principal_for_v62b") != "external_assistant_only":
        raise ValueError("V62-B evidence must preserve the external_assistant principal only")
    if payload.get("connector_hardening_selected_for_v62b") is not False:
        raise ValueError("V62-B evidence must preserve connector-hardening deferral")
    if payload.get("human_via_connector_selected_for_v62b") is not False:
        raise ValueError("V62-B evidence must preserve human-via-connector deferral")
    return payload


def _validate_v62c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V62C_EVIDENCE_SCHEMA:
        raise ValueError(
            "V63-A requires the shipped V62-C connector bridge hardening evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_connector_bridge_hardening_register@1"
    } - set(selected_shapes):
        raise ValueError("V62-C evidence must preserve the shipped connector hardening shape")
    required_true_fields = (
        "connector_bridge_hardening_register_must_be_typed_and_replayable",
        "hardening_register_consumes_shipped_v62a_basis",
        "hardening_register_consumes_shipped_v62b_basis",
        "hardening_register_consumes_shipped_v61a_v61b_v61c_basis",
        "candidate_outcomes_non_entitling_and_non_escalating_by_themselves",
        "committed_lane_artifacts_outrank_narrative_docs_for_v62c",
        "explicit_frozen_policy_anchor_required_for_replayability",
        "path_level_non_generalization_required_for_v62c",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V62-C evidence must preserve {field_name}")
    if payload.get("selected_connector_provider_for_v62c_basis") != "codex_only":
        raise ValueError("V62-C evidence must preserve the codex connector provider only")
    if payload.get("selected_connector_principal_for_v62c") != "external_assistant_only":
        raise ValueError("V62-C evidence must preserve the external_assistant principal only")
    if payload.get("selected_recommended_outcome_for_v62c") != (
        "candidate_for_later_connector_hardening"
    ):
        raise ValueError("V62-C evidence must preserve the advisory connector-hardening outcome")
    if payload.get("remote_operator_law_selected_for_v62c") is not False:
        raise ValueError("V62-C evidence must preserve remote-operator deferral")
    if payload.get("repo_or_execute_authority_selected_for_v62c") is not False:
        raise ValueError("V62-C evidence must preserve repo/execute deferral")
    if payload.get("dispatch_widening_selected_for_v62c") is not False:
        raise ValueError("V62-C evidence must preserve dispatch deferral")
    return payload


def _validate_v63a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V63A_EVIDENCE_SCHEMA:
        raise ValueError(
            "V63-B requires the shipped V63-A remote-operator evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_remote_operator_session_record@1",
        "agentic_de_remote_operator_view_packet@1",
        "agentic_de_remote_operator_response_record@1",
    } - set(selected_shapes):
        raise ValueError("V63-A evidence must preserve the shipped remote-operator starter shapes")
    if payload.get("selected_remote_operator_principal_for_v63a") != "remote_operator_only":
        raise ValueError("V63-A evidence must preserve the remote_operator principal only")
    if (
        payload.get("selected_remote_surface_class_for_v63a")
        != "read_mostly_phone_safe_remote_operator_surface_only"
    ):
        raise ValueError("V63-A evidence must preserve the shipped remote surface class only")
    if (
        payload.get("selected_consumed_v60_lineage_for_v63a")
        != "shipped_v60_continuation_lineage_only"
    ):
        raise ValueError("V63-A evidence must preserve shipped V60 continuation lineage only")
    if (
        payload.get("selected_consumed_v61_lineage_for_v63a")
        != "shipped_v61_governed_communication_lineage_only"
    ):
        raise ValueError("V63-A evidence must preserve shipped V61 communication lineage only")
    if payload.get("path_level_non_generalization_required_for_v63a") is not True:
        raise ValueError("V63-A evidence must preserve path-level non-generalization")
    if payload.get("repo_or_execute_authority_selected_for_v63a") is not False:
        raise ValueError("V63-A evidence must preserve repo/execute deferral")
    if payload.get("dispatch_widening_selected_for_v63a") is not False:
        raise ValueError("V63-A evidence must preserve dispatch deferral")
    return payload


def _validate_v63b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V63B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V63-C requires the shipped V63-B remote-operator control-bridge evidence "
            "payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_remote_operator_control_bridge_packet@1"
    } - set(selected_shapes):
        raise ValueError("V63-B evidence must preserve the shipped control-bridge shape")
    required_true_fields = (
        "bridge_packet_must_be_typed_and_replayable",
        "same_admitted_remote_session_plus_same_selected_intervention_kind_plus_same_consumed_basis_plus_same_frozen_policy_yields_same_bridge_packet",
        "structured_answer_consumes_explicit_shipped_context_only",
        "clarification_consumes_explicit_shipped_context_only",
        "inspect_rich_consumes_explicit_shipped_context_only",
        "structured_answer_is_not_charter_or_residual_or_continuation_or_communication_mutation_by_itself",
        "clarification_is_not_charter_or_residual_or_continuation_or_communication_mutation_by_itself",
        "inspect_rich_is_not_charter_or_residual_or_continuation_or_communication_mutation_by_itself",
        "richer_intervention_packet_is_not_bridge_office_or_act_authority_by_itself",
        "consumed_shipped_v63a_view_basis_ref_explicit",
        "path_level_non_generalization_required_for_v63b",
        "selected_bridge_path_may_not_generalize_by_default_into_all_device_or_all_surface_law",
    )
    all_surface_non_generalization_field = (
        "selected_bridge_path_may_not_generalize_by_default_into_all_device_or_all_surface_law"
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            if field_name == all_surface_non_generalization_field:
                raise ValueError(
                    "V63-B evidence must preserve all-device/all-surface non-generalization"
                )
            raise ValueError(f"V63-B evidence must preserve {field_name}")
    if payload.get("selected_remote_operator_principal_for_v63b") != "remote_operator_only":
        raise ValueError("V63-B evidence must preserve the remote_operator principal only")
    if (
        payload.get("selected_consumed_v63a_lineage_for_v63b")
        != "shipped_v63a_session_and_view_lineage_only"
    ):
        raise ValueError("V63-B evidence must preserve the shipped V63-A lineage only")
    if payload.get("repo_or_execute_authority_selected_for_v63b") is not False:
        raise ValueError("V63-B evidence must preserve repo/execute deferral")
    if payload.get("dispatch_widening_selected_for_v63b") is not False:
        raise ValueError("V63-B evidence must preserve dispatch deferral")
    return payload


def _validate_v64a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V64A_EVIDENCE_SCHEMA:
        raise ValueError(
            "V64-B requires the shipped V64-A repo writable-surface evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list):
        raise ValueError("V64-A evidence must preserve the shipped writable-surface shapes")
    if any(not isinstance(shape, str) for shape in selected_shapes):
        raise ValueError("V64-A evidence selected_record_shapes must be a list of strings")
    if {
        "agentic_de_repo_writable_surface_descriptor@1",
        "agentic_de_repo_write_lease_record@1",
        "agentic_de_repo_write_surface_admission_record@1",
    } - set(selected_shapes):
        raise ValueError("V64-A evidence must preserve the shipped writable-surface shapes")
    required_true_fields = (
        "writable_surface_descriptor_must_be_typed_and_replayable",
        "repo_write_lease_must_be_typed_and_replayable",
        "repo_write_surface_admission_must_be_typed_and_replayable",
        "same_selected_surface_basis_plus_same_shipped_basis_plus_same_frozen_policy_yields_same_descriptor_lease_and_admission_outputs",
        "surface_widening_only_in_v64a",
        "mutation_semantics_preserved_from_current_narrow_subset_in_v64a",
        "continuity_region_not_equivalent_to_writable_surface_descriptor_in_v64a",
        "communication_basis_may_contextualize_but_not_mint_writable_surface_authority_in_v64a",
        "canonical_normalized_path_membership_required_for_v64a",
        "explicit_inclusion_and_exclusion_basis_required_for_v64a",
        "symlink_alias_or_indirection_surprises_fail_closed_for_v64a",
        "per_target_occupancy_or_admissibility_law_required_inside_selected_surface_for_v64a",
        "lease_alone_not_blanket_entitlement_for_all_paths_in_surface_for_v64a",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V64-A evidence must preserve {field_name}")
    if (
        payload.get("selected_consumed_v59_lineage_for_v64a")
        != "shipped_v59_continuity_lineage_only"
    ):
        raise ValueError("V64-A evidence must preserve shipped V59 continuity lineage only")
    if (
        payload.get("selected_consumed_v60_lineage_for_v64a")
        != "shipped_v60_continuation_lineage_only"
    ):
        raise ValueError("V64-A evidence must preserve shipped V60 continuation lineage only")
    if (
        payload.get("selected_consumed_v61_lineage_for_v64a")
        != "shipped_v61_governed_communication_lineage_only"
    ):
        raise ValueError("V64-A evidence must preserve shipped V61 communication lineage only")
    if payload.get("selected_downstream_action_class_for_v64a") != "local_write":
        raise ValueError("V64-A evidence must preserve local_write only")
    if payload.get("selected_downstream_write_kind_for_v64a") != "create_new":
        raise ValueError("V64-A evidence must preserve create_new only")
    if payload.get("selected_all_repo_authority_for_v64a") is not False:
        raise ValueError("V64-A evidence must preserve all-repo deferral")
    if payload.get("selected_execute_authority_for_v64a") is not False:
        raise ValueError("V64-A evidence must preserve execute deferral")
    if payload.get("selected_dispatch_authority_for_v64a") is not False:
        raise ValueError("V64-A evidence must preserve dispatch deferral")
    if payload.get("selected_delegated_worker_authority_for_v64a") is not False:
        raise ValueError("V64-A evidence must preserve delegated-worker deferral")
    return payload


def _validate_v64b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V64B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V64-C requires the shipped V64-B repo write restoration evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list):
        raise ValueError("V64-B evidence must preserve the shipped restoration shapes")
    if any(not isinstance(shape, str) for shape in selected_shapes):
        raise ValueError("V64-B evidence selected_record_shapes must be a list of strings")
    if {
        "agentic_de_repo_write_restoration_record@1",
        "agentic_de_repo_write_reintegration_report@1",
    } - set(selected_shapes):
        raise ValueError("V64-B evidence must preserve the shipped restoration shapes")
    required_true_fields = (
        "repo_write_restoration_record_must_be_typed_and_replayable",
        "repo_write_reintegration_report_must_be_typed_and_replayable",
        "same_shipped_v64a_basis_plus_same_exact_target_plus_same_consumed_basis_plus_same_frozen_policy_yields_same_restoration_and_reintegration_outputs",
        "restoration_outputs_fail_closed_on_missing_or_inconsistent_basis",
        "restoration_may_not_overread_non_admitted_or_out_of_surface_targets",
        "target_membership_and_target_occupancy_or_admissibility_carry_through_must_remain_explicit_for_v64b",
        "restoration_is_not_fresh_surface_selection_or_fresh_lease_issuance_by_itself",
        "restoration_is_not_fresh_target_admission_by_itself",
        "mutation_semantics_preserved_from_v64a_in_v64b",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V64-B evidence must preserve {field_name}")
    if (
        payload.get("selected_consumed_v64a_lineage_for_v64b")
        != "shipped_v64a_descriptor_lease_and_admission_lineage_only"
    ):
        raise ValueError("V64-B evidence must preserve the shipped V64-A lineage only")
    if (
        payload.get("selected_concrete_write_effect_lineage_for_v64b")
        != "shipped_exact_observed_and_admitted_write_effect_lineage_only"
    ):
        raise ValueError("V64-B evidence must preserve the shipped exact write-effect lineage")
    if (
        payload.get("selected_consumed_v59_lineage_for_v64b")
        != "shipped_v59_continuity_lineage_only"
    ):
        raise ValueError("V64-B evidence must preserve shipped V59 continuity lineage only")
    if (
        payload.get("selected_consumed_v60_lineage_for_v64b")
        != "shipped_v60_continuation_lineage_only"
    ):
        raise ValueError("V64-B evidence must preserve shipped V60 continuation lineage only")
    if (
        payload.get("selected_consumed_v61_lineage_for_v64b")
        != "shipped_v61_governed_communication_lineage_only"
    ):
        raise ValueError("V64-B evidence must preserve shipped V61 communication lineage only")
    if payload.get("same_selected_writable_surface_only_for_v64b") is not True:
        raise ValueError("V64-B evidence must preserve same selected writable surface only")
    if payload.get("same_exact_admitted_target_only_for_v64b") is not True:
        raise ValueError("V64-B evidence must preserve same exact admitted target only")
    if payload.get("fresh_surface_selection_selected_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve fresh surface-selection deferral")
    if payload.get("fresh_lease_issuance_selected_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve fresh lease-issuance deferral")
    if payload.get("broader_per_surface_target_authority_selected_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve broader target-authority deferral")
    if payload.get("selected_all_repo_authority_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve all-repo deferral")
    if payload.get("selected_shell_authority_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve shell deferral")
    if payload.get("selected_execute_authority_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve execute deferral")
    if payload.get("selected_dispatch_authority_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve dispatch deferral")
    if payload.get("selected_delegated_worker_authority_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve delegated-worker deferral")
    if payload.get("selected_connector_law_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve connector deferral")
    if payload.get("selected_remote_operator_law_for_v64b") is not False:
        raise ValueError("V64-B evidence must preserve remote-operator deferral")
    return payload


def _validate_v64c_evidence_payload_for_v65a(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V64C_EVIDENCE_SCHEMA:
        raise ValueError(
            "V65-A requires the shipped V64-C repo writable-surface hardening evidence payload "
            "on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list):
        raise ValueError("V64-C evidence must preserve the shipped hardening shape")
    if any(not isinstance(shape, str) for shape in selected_shapes):
        raise ValueError("V64-C evidence selected_record_shapes must be a list of strings")
    if "agentic_de_repo_writable_surface_hardening_register@1" not in selected_shapes:
        raise ValueError("V64-C evidence must preserve the shipped hardening shape")
    required_true_fields = (
        "advisory_only",
        "candidate_only",
        "committed_lane_artifacts_outrank_narrative_docs_for_v64c",
        "evidence_basis_distinct_from_recommendation_required_in_v64c",
        "explicit_frozen_policy_anchor_required_for_replayability",
        "writable_surface_hardening_recommendation_must_be_extensional_and_replayable",
        "lineage_root_non_independence_dedup_required_in_v64c",
        "preserved_write_semantics_summary_required_in_v64c",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V64-C evidence must preserve {field_name}")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V64-C evidence must preserve changes_live_behavior_by_default=false")
    if payload.get("delegated_worker_authority_selected_for_v64c") is not False:
        raise ValueError("V64-C evidence must preserve delegated-worker deferral")
    return payload


def _validate_v48e_evidence_payload_for_v65a(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V48E_EVIDENCE_SCHEMA:
        raise ValueError(
            "V65-A requires the released V48-E worker delegation topology evidence payload "
            "on main"
        )
    if payload.get("accepted_completed_fixture_path") != (
        "packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology.json"
    ):
        raise ValueError("V48-E evidence must preserve the released completed topology fixture")
    if payload.get("typed_rejected_fixture_path") != (
        "packages/adeu_agent_harness/tests/fixtures/v48e/"
        "reference_worker_delegation_topology_rejected_compiled_boundary_mismatch.json"
    ):
        raise ValueError("V48-E evidence must preserve the released rejected topology fixture")
    if payload.get("typed_incomplete_lineage_fixture_path") != (
        "packages/adeu_agent_harness/tests/fixtures/v48e/"
        "reference_worker_delegation_topology_incomplete_lineage.json"
    ):
        raise ValueError("V48-E evidence must preserve the released incomplete topology fixture")
    return payload


def _validate_v65a_evidence_payload_for_v65b(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V65A_EVIDENCE_SCHEMA:
        raise ValueError(
            "V65-B requires the shipped V65-A delegated worker export evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list):
        raise ValueError("V65-A evidence must preserve the shipped export shape")
    if any(not isinstance(shape, str) for shape in selected_shapes):
        raise ValueError("V65-A evidence selected_record_shapes must be a list of strings")
    if "agentic_de_delegated_worker_export_packet@1" not in selected_shapes:
        raise ValueError("V65-A evidence must preserve the shipped export shape")
    required_true_fields = (
        "delegated_export_packet_must_be_typed_and_replayable",
        "canonical_exported_work_membership_required_for_v65a",
        "exact_target_or_patch_or_artifact_summary_required_for_v65a",
        "mutation_semantics_preserved_from_shipped_v64_subset_in_v65a",
        "export_bridge_only_in_v65a",
        "delegated_export_packet_is_not_reconciliation_by_itself_in_v65a",
        "delegated_export_packet_does_not_carry_worker_result_semantics_yet_in_v65a",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V65-A evidence must preserve {field_name}")
    if payload.get("selected_consumed_v60_lineage_for_v65a") != (
        "shipped_v60_continuation_lineage_only"
    ):
        raise ValueError("V65-A evidence must preserve shipped V60 continuation lineage only")
    if payload.get("selected_consumed_v61_lineage_for_v65a") != (
        "shipped_v61_governed_communication_lineage_only"
    ):
        raise ValueError("V65-A evidence must preserve shipped V61 communication lineage only")
    return payload


def _validate_v48d_evidence_payload_for_v65b(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V48D_EVIDENCE_SCHEMA:
        raise ValueError(
            "V65-B requires the released V48-D worker boundary conformance evidence payload "
            "on main"
        )
    if payload.get("accepted_conformant_fixture_path") != (
        "packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report.json"
    ):
        raise ValueError(
            "V48-D evidence must preserve the released conformant worker boundary "
            "conformance fixture"
        )
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
        raise ValueError("V58-C requires the shipped V58-B live restoration reintegration surface")
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
    selected_target = "observed_and_restored_v57a_create_new_exemplar_only"
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
        "writes_allowed_enabled" if live_turn_snapshot.writes_allowed else "writes_allowed_disabled"
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
    if reintegration.target_arc != V58A_TARGET_ARC or reintegration.target_path != V58A_TARGET_PATH:
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
        raise ValueError("V58-B restoration-time cwd must resolve to the admitted repository root")
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
    v58a_reintegration_path = _resolve_path(repo_root_path=root, path=v58a_reintegration_path)
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
    v58a_reintegration_path = _resolve_path(repo_root_path=root, path=v58a_reintegration_path)
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
    if continuity_reintegration.live_turn_reintegration_ref != live_turn_reintegration.report_id:
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
    if continuity_reintegration.local_effect_conformance_ref != conformance.report_id:
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
        raise ValueError("V59-B restoration-time cwd must resolve to the admitted repository root")
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
        raise ValueError("V59-C requires the shipped V59-B continuity restoration reintegration")
    if continuity_restoration_handoff.evidence_only is not True:
        raise ValueError("V59-C requires the shipped evidence-only V59-B handoff posture")
    if continuity_restoration_handoff.changes_live_behavior_by_default:
        raise ValueError("V59-C requires the shipped non-live V59-B handoff posture")
    if continuity_restoration_reintegration.evidence_only is not True:
        raise ValueError("V59-C requires the shipped evidence-only V59-B reintegration posture")
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
    if continuity_restoration_handoff.prior_governed_state_baseline_match_verdict != "matched":
        raise ValueError("V59-C requires the shipped matched V59-B baseline posture")
    if continuity_restoration_handoff.selected_restoration_scope != V59B_SELECTED_RESTORATION_SCOPE:
        raise ValueError("V59-B handoff must preserve the shipped bounded restoration scope")
    if continuity_restoration_reintegration.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError("V59-B reintegration does not bind the shipped V59-A admission lineage")
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
        prior_governed_state_baseline_match_verdict=(prior_governed_state_baseline_match_verdict),
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
        six_lane_closeout_posture = "current_turn_continuity_restoration_blocked_boundedness_failed"
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
            "V60-A current approval posture snapshot must match the shipped V59-A admission posture"
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
        raise ValueError("V59-C hardening does not bind the shipped continuity restoration handoff")
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
    target_relative_path: str,
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
            "local_write/create_new exemplar over "
            f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
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
    for field_name, candidate in (
        ("domain_packet_path", domain_packet_path),
        ("morph_ir_path", morph_ir_path),
        ("interaction_contract_path", interaction_contract_path),
        ("action_proposal_path", action_proposal_path),
        ("v56a_checkpoint_path", v56a_checkpoint_path),
        ("v56a_diagnostics_path", v56a_diagnostics_path),
        ("v56a_conformance_path", v56a_conformance_path),
        ("v56b_lane_drift_path", v56b_lane_drift_path),
        ("v56b_action_class_taxonomy_path", v56b_action_class_taxonomy_path),
        ("v56b_runtime_state_path", v56b_runtime_state_path),
        ("v56b_action_ticket_path", v56b_action_ticket_path),
        ("v56b_diagnostics_path", v56b_diagnostics_path),
        ("v56b_conformance_path", v56b_conformance_path),
        ("v56c_lane_drift_path", v56c_lane_drift_path),
        ("v56c_runtime_harvest_path", v56c_runtime_harvest_path),
        ("v56c_governance_calibration_path", v56c_governance_calibration_path),
        ("v56c_migration_decision_path", v56c_migration_decision_path),
        ("v59a_lane_drift_path", v59a_lane_drift_path),
        ("v59a_continuity_region_path", v59a_continuity_region_path),
        ("v59a_continuity_admission_path", v59a_continuity_admission_path),
        ("v59a_occupancy_path", v59a_occupancy_path),
        ("v59a_live_turn_admission_path", v59a_live_turn_admission_path),
        ("v59a_live_turn_handoff_path", v59a_live_turn_handoff_path),
        ("v59a_observation_path", v59a_observation_path),
        ("v59a_local_effect_conformance_path", v59a_local_effect_conformance_path),
        ("v59a_live_turn_reintegration_path", v59a_live_turn_reintegration_path),
        ("v59a_continuity_reintegration_path", v59a_continuity_reintegration_path),
        ("v59b_lane_drift_path", v59b_lane_drift_path),
        (
            "v59b_continuity_restoration_handoff_path",
            v59b_continuity_restoration_handoff_path,
        ),
        ("v59b_restoration_path", v59b_restoration_path),
        (
            "v59b_continuity_restoration_reintegration_path",
            v59b_continuity_restoration_reintegration_path,
        ),
        ("v59c_lane_drift_path", v59c_lane_drift_path),
        ("v59c_hardening_path", v59c_hardening_path),
        ("lane_drift_path", lane_drift_path),
        ("seed_intent_path", seed_intent_path),
        ("v56a_evidence_path", v56a_evidence_path),
        ("v56b_evidence_path", v56b_evidence_path),
        ("v56c_evidence_path", v56c_evidence_path),
        ("v57a_evidence_path", v57a_evidence_path),
        ("v57b_evidence_path", v57b_evidence_path),
        ("v57c_evidence_path", v57c_evidence_path),
        ("v58a_evidence_path", v58a_evidence_path),
        ("v58b_evidence_path", v58b_evidence_path),
        ("v58c_evidence_path", v58c_evidence_path),
        ("v59a_evidence_path", v59a_evidence_path),
        ("v59b_evidence_path", v59b_evidence_path),
        ("v59c_evidence_path", v59c_evidence_path),
    ):
        _assert_v60a_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )

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
        target_relative_path=target_relative_path,
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


def _validate_v60a_continuation_surfaces(
    *,
    seed_intent: AgenticDeSeedIntentRecord,
    task_charter: AgenticDeTaskCharterPacket,
    task_residual: AgenticDeTaskResidualPacket,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_decision: AgenticDeContinuationDecisionRecord,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    target_relative_path: str,
) -> None:
    expected_path_summary = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if seed_intent.target_arc != V60A_TARGET_ARC or seed_intent.target_path != V60A_TARGET_PATH:
        raise ValueError("V60-B requires the shipped V60-A seed intent surface")
    if task_charter.target_arc != V60A_TARGET_ARC or task_charter.target_path != V60A_TARGET_PATH:
        raise ValueError("V60-B requires the shipped V60-A task charter surface")
    if task_residual.target_arc != V60A_TARGET_ARC or task_residual.target_path != V60A_TARGET_PATH:
        raise ValueError("V60-B requires the shipped V60-A task residual surface")
    if (
        loop_state_ledger.target_arc != V60A_TARGET_ARC
        or loop_state_ledger.target_path != V60A_TARGET_PATH
    ):
        raise ValueError("V60-B requires the shipped V60-A loop-state ledger surface")
    if (
        continuation_decision.target_arc != V60A_TARGET_ARC
        or continuation_decision.target_path != V60A_TARGET_PATH
    ):
        raise ValueError("V60-B requires the shipped V60-A continuation decision surface")
    if task_charter.seed_intent_ref != seed_intent.seed_intent_id:
        raise ValueError("V60-A task charter does not bind the provided seed intent")
    if task_residual.task_charter_ref != task_charter.charter_id:
        raise ValueError("V60-A task residual does not bind the provided task charter")
    if loop_state_ledger.task_charter_ref != task_charter.charter_id:
        raise ValueError("V60-A loop-state ledger does not bind the provided task charter")
    if loop_state_ledger.task_residual_ref != task_residual.residual_id:
        raise ValueError("V60-A loop-state ledger does not bind the provided task residual")
    if continuation_decision.loop_state_ledger_ref != loop_state_ledger.ledger_id:
        raise ValueError("V60-A continuation decision does not bind the provided loop ledger")
    if task_charter.selected_downstream_path_summary != expected_path_summary:
        raise ValueError("V60-B requires the shipped exact V60-A selected path")
    if continuation_decision.selected_next_path_summary != expected_path_summary:
        raise ValueError("V60-B requires the shipped exact V60-A selected-next path")
    if continuation_decision.continuation_outcome != "continue_to_governed_act":
        raise ValueError("V60-B requires the shipped continuing V60-A continuation posture")
    if continuation_decision.frozen_policy_anchor_ref != V60A_FROZEN_POLICY_REF:
        raise ValueError("V60-B requires the shipped V60-A frozen policy anchor")
    if (
        task_residual.latest_live_turn_reintegration_ref_or_none
        != live_turn_reintegration.report_id
    ):
        raise ValueError("V60-A task residual does not preserve the shipped latest live turn")
    if (
        task_residual.latest_continuity_reintegration_ref_or_none
        != continuity_reintegration.report_id
    ):
        raise ValueError(
            "V60-A task residual does not preserve the shipped latest continuity reintegration"
        )
    if (
        loop_state_ledger.latest_live_turn_reintegration_ref_or_none
        != live_turn_reintegration.report_id
    ):
        raise ValueError("V60-A loop-state ledger does not preserve the shipped latest live turn")
    if (
        loop_state_ledger.latest_continuity_reintegration_ref_or_none
        != continuity_reintegration.report_id
    ):
        raise ValueError(
            "V60-A loop-state ledger does not preserve the shipped latest continuity reintegration"
        )


def _select_v60b_latest_reintegrated_act(
    *,
    prior_task_residual: AgenticDeTaskResidualPacket,
    prior_loop_state_ledger: AgenticDeLoopStateLedger,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport | None
    ),
) -> tuple[str, str]:
    if live_turn_reintegration.reintegration_status != "reintegrated":
        raise ValueError("V60-B requires one latest reintegrated live-turn act lineage only")
    if continuity_reintegration.continuity_reintegration_status != "reintegrated":
        raise ValueError("V60-B requires one latest reintegrated continuity act lineage only")
    if (
        prior_task_residual.latest_live_turn_reintegration_ref_or_none
        != live_turn_reintegration.report_id
    ):
        raise ValueError(
            "V60-B latest live-turn reintegration selection must match the shipped "
            "V60-A residual anchor"
        )
    if (
        prior_task_residual.latest_continuity_reintegration_ref_or_none
        != continuity_reintegration.report_id
    ):
        raise ValueError(
            "V60-B latest continuity reintegration selection must match the shipped "
            "V60-A residual anchor"
        )
    if (
        prior_loop_state_ledger.latest_live_turn_reintegration_ref_or_none
        != live_turn_reintegration.report_id
    ):
        raise ValueError(
            "V60-B latest live-turn reintegration selection must match the shipped "
            "V60-A loop anchor"
        )
    if (
        prior_loop_state_ledger.latest_continuity_reintegration_ref_or_none
        != continuity_reintegration.report_id
    ):
        raise ValueError(
            "V60-B latest continuity reintegration selection must match the shipped "
            "V60-A loop anchor"
        )
    restoration_ref_or_none: str | None = None
    if continuity_restoration_reintegration is not None:
        if continuity_restoration_reintegration.continuity_restoration_reintegration_status != (
            "reintegrated"
        ):
            raise ValueError(
                (
                    "V60-B latest continuity restoration reintegration must be reintegrated "
                    "when supplied"
                )
            )
        restoration_ref_or_none = continuity_restoration_reintegration.report_id
    latest_identity = (
        "latest_reintegrated_act::"
        f"{live_turn_reintegration.report_id}::"
        f"{continuity_reintegration.report_id}::"
        f"{restoration_ref_or_none or 'none'}"
    )
    selection_basis_summary = (
        "explicit latest-act tuple over shipped V59 lineage: live_turn_reintegration + "
        "continuity_reintegration + continuity_restoration_reintegration_or_none; "
        "ambiguity blocks refresh"
    )
    return latest_identity, selection_basis_summary


def _build_v60b_task_residual_refresh_packet(
    *,
    prior_task_charter: AgenticDeTaskCharterPacket,
    prior_task_residual: AgenticDeTaskResidualPacket,
    prior_loop_state_ledger: AgenticDeLoopStateLedger,
    prior_continuation_decision: AgenticDeContinuationDecisionRecord,
    latest_reintegrated_act_identity: str,
    latest_reintegrated_act_selection_basis_summary: str,
    latest_live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    latest_continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    latest_continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport | None
    ),
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeTaskResidualRefreshPacket:
    field_origin_tags = {
        "latest_reintegrated_act_selection_basis_summary": "current_turn_derived",
        "refreshed_frontier_summary": "current_turn_derived",
        "refreshed_open_obligation_summary": "current_turn_derived",
        "refreshed_blocker_summary": "current_turn_derived",
        "refreshed_owed_communication_posture_summary": "current_turn_derived",
        "residual_refresh_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "latest_reintegrated_act_selection_basis_summary": [
            prior_loop_state_ledger.ledger_id,
            latest_live_turn_reintegration.report_id,
            latest_continuity_reintegration.report_id,
            *(
                [latest_continuity_restoration_reintegration.report_id]
                if latest_continuity_restoration_reintegration is not None
                else []
            ),
        ],
        "refreshed_frontier_summary": [
            prior_task_residual.residual_id,
            prior_continuation_decision.decision_id,
        ],
        "refreshed_open_obligation_summary": [
            prior_task_residual.residual_id,
            V60B_FROZEN_POLICY_REF,
        ],
        "refreshed_blocker_summary": [
            prior_task_residual.residual_id,
            latest_live_turn_reintegration.report_id,
        ],
        "refreshed_owed_communication_posture_summary": [
            prior_task_residual.residual_id,
            V60B_FROZEN_POLICY_REF,
        ],
        "residual_refresh_basis_summary": [
            prior_task_charter.charter_id,
            prior_task_residual.residual_id,
            prior_loop_state_ledger.ledger_id,
            prior_continuation_decision.decision_id,
            latest_live_turn_reintegration.report_id,
            latest_continuity_reintegration.report_id,
            *(
                [latest_continuity_restoration_reintegration.report_id]
                if latest_continuity_restoration_reintegration is not None
                else []
            ),
            V60B_FROZEN_POLICY_REF,
        ],
    }
    root_origin_ids = [
        f"loop:{prior_loop_state_ledger.ledger_id}",
        f"residual:{prior_task_residual.residual_id}",
        f"decision:{prior_continuation_decision.decision_id}",
        f"latest_act:{latest_reintegrated_act_identity}",
        f"policy:{V60B_FROZEN_POLICY_REF}",
    ]
    return AgenticDeTaskResidualRefreshPacket(
        target_arc=V60B_TARGET_ARC,
        target_path=V60B_TARGET_PATH,
        prior_task_charter_ref=prior_task_charter.charter_id,
        prior_task_residual_ref=prior_task_residual.residual_id,
        prior_loop_state_ledger_ref=prior_loop_state_ledger.ledger_id,
        prior_loop_identity_ref=prior_loop_state_ledger.ledger_id,
        prior_continuation_decision_ref=prior_continuation_decision.decision_id,
        latest_reintegrated_act_identity=latest_reintegrated_act_identity,
        latest_reintegrated_act_selection_basis_summary=(
            latest_reintegrated_act_selection_basis_summary
        ),
        latest_live_turn_reintegration_ref=latest_live_turn_reintegration.report_id,
        latest_continuity_reintegration_ref=latest_continuity_reintegration.report_id,
        latest_continuity_restoration_reintegration_ref_or_none=(
            latest_continuity_restoration_reintegration.report_id
            if latest_continuity_restoration_reintegration is not None
            else None
        ),
        refreshed_frontier_summary=prior_task_residual.current_frontier_summary,
        refreshed_open_obligation_summary=prior_task_residual.open_obligation_summary,
        refreshed_blocker_summary=prior_task_residual.blocker_summary,
        refreshed_open_approval_refs=prior_task_residual.open_approval_refs,
        refreshed_owed_communication_posture_summary=(
            prior_task_residual.owed_communication_posture_summary
        ),
        residual_refresh_basis_summary=(
            "shipped V60-A charter/residual/loop/decision + explicit latest reintegrated act "
            "selection + frozen V60-B policy anchor over the exact shipped downstream path"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=evidence_refs,
    )


def _build_v60b_continuation_refresh_decision_record(
    *,
    prior_task_residual: AgenticDeTaskResidualPacket,
    prior_loop_state_ledger: AgenticDeLoopStateLedger,
    refreshed_task_residual: AgenticDeTaskResidualRefreshPacket,
    latest_reintegrated_act_identity: str,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeContinuationRefreshDecisionRecord:
    selected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if prior_task_residual.blocker_summary != "none_under_current_v60a_policy":
        refresh_outcome = "reproposal_required"
        refresh_reason_codes = [
            "stable_loop_identity_preserved",
            "latest_reintegrated_act_selected_explicitly",
            "current_frontier_cannot_continue_as_is",
            "reproposal_posture_only_not_seed_ingress",
            "communication_law_still_deferred_to_v61",
        ]
        selected_next_path_summary_or_none = None
        reproposal_basis_summary_or_none = (
            "current charter / residual frontier may not lawfully continue as-is under "
            "frozen V60-B policy; later structured ingress or governed communication is needed"
        )
    elif prior_task_residual.open_approval_refs:
        refresh_outcome = "await_authority"
        refresh_reason_codes = [
            "stable_loop_identity_preserved",
            "latest_reintegrated_act_selected_explicitly",
            "open_approval_still_required",
            "single_step_local_ticket_duration_preserved",
        ]
        selected_next_path_summary_or_none = None
        reproposal_basis_summary_or_none = None
    else:
        refresh_outcome = "continue_to_governed_act"
        refresh_reason_codes = [
            "stable_loop_identity_preserved",
            "latest_reintegrated_act_selected_explicitly",
            "refreshed_residual_replayable",
            "exact_v59_downstream_path_preserved",
            "single_step_local_ticket_duration_preserved",
            "communication_law_still_deferred_to_v61",
        ]
        selected_next_path_summary_or_none = selected_path
        reproposal_basis_summary_or_none = None
    field_origin_tags = {
        "refresh_outcome": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "selected_next_path_summary_or_none": "current_turn_derived",
        "reproposal_basis_summary_or_none": "current_turn_derived",
    }
    field_dependence_tags = {
        "refresh_outcome": [
            prior_loop_state_ledger.ledger_id,
            refreshed_task_residual.refresh_packet_id,
            latest_reintegrated_act_identity,
            V60B_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [],
        "evidence_basis_summary": [
            prior_task_residual.residual_id,
            prior_loop_state_ledger.ledger_id,
            refreshed_task_residual.refresh_packet_id,
            latest_reintegrated_act_identity,
            V60B_FROZEN_POLICY_REF,
        ],
        "selected_next_path_summary_or_none": (
            [refreshed_task_residual.refresh_packet_id, prior_loop_state_ledger.ledger_id]
            if selected_next_path_summary_or_none is not None
            else ["none_selected_under_current_v60b_policy"]
        ),
        "reproposal_basis_summary_or_none": (
            [prior_task_residual.residual_id, V60B_FROZEN_POLICY_REF]
            if reproposal_basis_summary_or_none is not None
            else ["none_under_current_v60b_policy"]
        ),
    }
    root_origin_ids = [
        f"loop:{prior_loop_state_ledger.ledger_id}",
        f"refresh:{refreshed_task_residual.refresh_packet_id}",
        f"latest_act:{latest_reintegrated_act_identity}",
        f"policy:{V60B_FROZEN_POLICY_REF}",
    ]
    return AgenticDeContinuationRefreshDecisionRecord(
        target_arc=V60B_TARGET_ARC,
        target_path=V60B_TARGET_PATH,
        prior_loop_state_ledger_ref=prior_loop_state_ledger.ledger_id,
        stable_loop_identity_ref=prior_loop_state_ledger.ledger_id,
        refreshed_task_residual_ref=refreshed_task_residual.refresh_packet_id,
        latest_reintegrated_act_identity=latest_reintegrated_act_identity,
        refresh_outcome=refresh_outcome,
        refresh_reason_codes=refresh_reason_codes,
        frozen_policy_anchor_ref=V60B_FROZEN_POLICY_REF,
        evidence_basis_summary=(
            "same shipped loop identity + same explicit latest reintegrated act + same "
            "frozen V60-B policy yields the same refresh outputs"
        ),
        selected_next_path_summary_or_none=selected_next_path_summary_or_none,
        reproposal_basis_summary_or_none=reproposal_basis_summary_or_none,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=evidence_refs,
    )


def run_agentic_de_continuation_v60b(
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
    v60a_lane_drift_path: Path = DEFAULT_V60A_LANE_DRIFT_PATH,
    v60a_seed_intent_path: Path = DEFAULT_V60A_SEED_INTENT_PATH,
    v60a_task_charter_path: Path = DEFAULT_V60A_TASK_CHARTER_PATH,
    v60a_task_residual_path: Path = DEFAULT_V60A_TASK_RESIDUAL_PATH,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60a_continuation_decision_path: Path = DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    lane_drift_path: Path = DEFAULT_V60B_LANE_DRIFT_PATH,
    v59a_evidence_path: Path = DEFAULT_V59A_EVIDENCE_PATH,
    v59b_evidence_path: Path = DEFAULT_V59B_EVIDENCE_PATH,
    v60a_evidence_path: Path = DEFAULT_V60A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> tuple[
    AgenticDeTaskResidualRefreshPacket,
    AgenticDeContinuationRefreshDecisionRecord,
]:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V60-B continuation")
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
    v60a_lane_drift_path = _resolve_path(repo_root_path=root, path=v60a_lane_drift_path)
    v60a_seed_intent_path = _resolve_path(repo_root_path=root, path=v60a_seed_intent_path)
    v60a_task_charter_path = _resolve_path(repo_root_path=root, path=v60a_task_charter_path)
    v60a_task_residual_path = _resolve_path(repo_root_path=root, path=v60a_task_residual_path)
    v60a_loop_state_ledger_path = _resolve_path(
        repo_root_path=root, path=v60a_loop_state_ledger_path
    )
    v60a_continuation_decision_path = _resolve_path(
        repo_root_path=root, path=v60a_continuation_decision_path
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v59a_evidence_path = _resolve_path(repo_root_path=root, path=v59a_evidence_path)
    v59b_evidence_path = _resolve_path(repo_root_path=root, path=v59b_evidence_path)
    v60a_evidence_path = _resolve_path(repo_root_path=root, path=v60a_evidence_path)
    for field_name, candidate in (
        ("domain_packet_path", domain_packet_path),
        ("morph_ir_path", morph_ir_path),
        ("interaction_contract_path", interaction_contract_path),
        ("action_proposal_path", action_proposal_path),
        ("v56a_checkpoint_path", v56a_checkpoint_path),
        ("v56a_diagnostics_path", v56a_diagnostics_path),
        ("v56a_conformance_path", v56a_conformance_path),
        ("v56b_lane_drift_path", v56b_lane_drift_path),
        ("v56b_action_class_taxonomy_path", v56b_action_class_taxonomy_path),
        ("v56b_runtime_state_path", v56b_runtime_state_path),
        ("v56b_action_ticket_path", v56b_action_ticket_path),
        ("v56b_diagnostics_path", v56b_diagnostics_path),
        ("v56b_conformance_path", v56b_conformance_path),
        ("v56c_lane_drift_path", v56c_lane_drift_path),
        ("v56c_runtime_harvest_path", v56c_runtime_harvest_path),
        ("v56c_governance_calibration_path", v56c_governance_calibration_path),
        ("v56c_migration_decision_path", v56c_migration_decision_path),
        ("v59a_lane_drift_path", v59a_lane_drift_path),
        ("v59a_continuity_region_path", v59a_continuity_region_path),
        ("v59a_continuity_admission_path", v59a_continuity_admission_path),
        ("v59a_occupancy_path", v59a_occupancy_path),
        ("v59a_live_turn_admission_path", v59a_live_turn_admission_path),
        ("v59a_live_turn_handoff_path", v59a_live_turn_handoff_path),
        ("v59a_observation_path", v59a_observation_path),
        ("v59a_local_effect_conformance_path", v59a_local_effect_conformance_path),
        ("v59a_live_turn_reintegration_path", v59a_live_turn_reintegration_path),
        ("v59a_continuity_reintegration_path", v59a_continuity_reintegration_path),
        ("v59b_lane_drift_path", v59b_lane_drift_path),
        ("v59b_continuity_restoration_handoff_path", v59b_continuity_restoration_handoff_path),
        ("v59b_restoration_path", v59b_restoration_path),
        (
            "v59b_continuity_restoration_reintegration_path",
            v59b_continuity_restoration_reintegration_path,
        ),
        ("v60a_lane_drift_path", v60a_lane_drift_path),
        ("v60a_seed_intent_path", v60a_seed_intent_path),
        ("v60a_task_charter_path", v60a_task_charter_path),
        ("v60a_task_residual_path", v60a_task_residual_path),
        ("v60a_loop_state_ledger_path", v60a_loop_state_ledger_path),
        ("v60a_continuation_decision_path", v60a_continuation_decision_path),
        ("lane_drift_path", lane_drift_path),
        ("v59a_evidence_path", v59a_evidence_path),
        ("v59b_evidence_path", v59b_evidence_path),
        ("v60a_evidence_path", v60a_evidence_path),
    ):
        _assert_v60b_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )

    _validate_v60b_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v60a_lane_drift_record(load_lane_drift_record(v60a_lane_drift_path))
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
    _validate_v60a_evidence_payload(
        _load_json_object(v60a_evidence_path, error_label="V60-A evidence")
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
    v60a_seed_intent = load_seed_intent_record(v60a_seed_intent_path)
    v60a_task_charter = load_task_charter_packet(v60a_task_charter_path)
    v60a_task_residual = load_task_residual_packet(v60a_task_residual_path)
    v60a_loop_state_ledger = load_loop_state_ledger(v60a_loop_state_ledger_path)
    v60a_continuation_decision = load_continuation_decision_record(v60a_continuation_decision_path)

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
    _validate_v60a_continuation_surfaces(
        seed_intent=v60a_seed_intent,
        task_charter=v60a_task_charter,
        task_residual=v60a_task_residual,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_decision=v60a_continuation_decision,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        target_relative_path=target_relative_path,
    )

    latest_reintegrated_act_identity, latest_reintegrated_act_selection_basis_summary = (
        _select_v60b_latest_reintegrated_act(
            prior_task_residual=v60a_task_residual,
            prior_loop_state_ledger=v60a_loop_state_ledger,
            live_turn_reintegration=v59a_live_turn_reintegration,
            continuity_reintegration=v59a_continuity_reintegration,
            continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        )
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
        _render_input_ref(repo_root_path=root, path=v60a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v60a_seed_intent_path),
        _render_input_ref(repo_root_path=root, path=v60a_task_charter_path),
        _render_input_ref(repo_root_path=root, path=v60a_task_residual_path),
        _render_input_ref(repo_root_path=root, path=v60a_loop_state_ledger_path),
        _render_input_ref(repo_root_path=root, path=v60a_continuation_decision_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v59b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v60a_evidence_path),
    ]
    refreshed_task_residual = _build_v60b_task_residual_refresh_packet(
        prior_task_charter=v60a_task_charter,
        prior_task_residual=v60a_task_residual,
        prior_loop_state_ledger=v60a_loop_state_ledger,
        prior_continuation_decision=v60a_continuation_decision,
        latest_reintegrated_act_identity=latest_reintegrated_act_identity,
        latest_reintegrated_act_selection_basis_summary=(
            latest_reintegrated_act_selection_basis_summary
        ),
        latest_live_turn_reintegration=v59a_live_turn_reintegration,
        latest_continuity_reintegration=v59a_continuity_reintegration,
        latest_continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        target_relative_path=target_relative_path,
        evidence_refs=evidence_refs,
    )
    refreshed_continuation_decision = _build_v60b_continuation_refresh_decision_record(
        prior_task_residual=v60a_task_residual,
        prior_loop_state_ledger=v60a_loop_state_ledger,
        refreshed_task_residual=refreshed_task_residual,
        latest_reintegrated_act_identity=latest_reintegrated_act_identity,
        target_relative_path=target_relative_path,
        evidence_refs=evidence_refs,
    )
    if (
        refreshed_continuation_decision.refresh_outcome == "continue_to_governed_act"
        and refreshed_continuation_decision.selected_next_path_summary_or_none
        != _expected_v60a_selected_downstream_path_summary(target_relative_path)
    ):
        raise ValueError(
            "V60-B continuation refresh decision must preserve the exact selected path"
        )
    return refreshed_task_residual, refreshed_continuation_decision


def _validate_v60b_refresh_surfaces(
    *,
    prior_task_charter: AgenticDeTaskCharterPacket,
    prior_task_residual: AgenticDeTaskResidualPacket,
    prior_loop_state_ledger: AgenticDeLoopStateLedger,
    prior_continuation_decision: AgenticDeContinuationDecisionRecord,
    refreshed_task_residual: AgenticDeTaskResidualRefreshPacket,
    refreshed_continuation_decision: AgenticDeContinuationRefreshDecisionRecord,
    latest_live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    latest_continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    latest_continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport
    ),
    target_relative_path: str,
) -> None:
    expected_path_summary = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if (
        refreshed_task_residual.target_arc != V60B_TARGET_ARC
        or refreshed_task_residual.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V60-C requires the shipped V60-B task residual refresh surface")
    if (
        refreshed_continuation_decision.target_arc != V60B_TARGET_ARC
        or refreshed_continuation_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V60-C requires the shipped V60-B continuation refresh decision surface")
    if refreshed_task_residual.prior_task_charter_ref != prior_task_charter.charter_id:
        raise ValueError("V60-B task residual refresh does not bind the shipped V60-A charter")
    if refreshed_task_residual.prior_task_residual_ref != prior_task_residual.residual_id:
        raise ValueError("V60-B task residual refresh does not bind the shipped V60-A residual")
    if refreshed_task_residual.prior_loop_state_ledger_ref != prior_loop_state_ledger.ledger_id:
        raise ValueError("V60-B task residual refresh does not bind the shipped V60-A loop")
    if refreshed_task_residual.prior_loop_identity_ref != prior_loop_state_ledger.ledger_id:
        raise ValueError("V60-B task residual refresh must preserve the stable loop identity")
    if (
        refreshed_task_residual.prior_continuation_decision_ref
        != prior_continuation_decision.decision_id
    ):
        raise ValueError("V60-B task residual refresh does not bind the shipped V60-A decision")
    if (
        refreshed_task_residual.latest_live_turn_reintegration_ref
        != latest_live_turn_reintegration.report_id
    ):
        raise ValueError(
            "V60-B task residual refresh does not preserve the shipped latest live turn"
        )
    if (
        refreshed_task_residual.latest_continuity_reintegration_ref
        != latest_continuity_reintegration.report_id
    ):
        raise ValueError(
            "V60-B task residual refresh does not preserve the shipped latest continuity "
            "reintegration"
        )
    if (
        refreshed_task_residual.latest_continuity_restoration_reintegration_ref_or_none
        != latest_continuity_restoration_reintegration.report_id
    ):
        raise ValueError(
            "V60-B task residual refresh does not preserve the shipped latest continuity "
            "restoration reintegration"
        )
    if (
        refreshed_continuation_decision.prior_loop_state_ledger_ref
        != prior_loop_state_ledger.ledger_id
    ):
        raise ValueError("V60-B continuation refresh decision does not bind the shipped V60-A loop")
    if (
        refreshed_continuation_decision.stable_loop_identity_ref
        != prior_loop_state_ledger.ledger_id
    ):
        raise ValueError("V60-B continuation refresh decision must preserve stable loop identity")
    if (
        refreshed_continuation_decision.refreshed_task_residual_ref
        != refreshed_task_residual.refresh_packet_id
    ):
        raise ValueError(
            "V60-B continuation refresh decision does not bind the shipped refresh packet"
        )
    if (
        refreshed_continuation_decision.latest_reintegrated_act_identity
        != refreshed_task_residual.latest_reintegrated_act_identity
    ):
        raise ValueError("V60-B continuation refresh decision must preserve latest-act identity")
    if (
        refreshed_continuation_decision.refresh_outcome != "continue_to_governed_act"
        or refreshed_continuation_decision.selected_next_path_summary_or_none
        != expected_path_summary
        or refreshed_continuation_decision.reproposal_basis_summary_or_none is not None
    ):
        raise ValueError("V60-C requires the shipped exact V60-B continuing refresh posture")
    if refreshed_continuation_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V60-C requires the shipped V60-B frozen policy anchor")
    required_reason_codes = [
        "stable_loop_identity_preserved",
        "latest_reintegrated_act_selected_explicitly",
        "refreshed_residual_replayable",
        "exact_v59_downstream_path_preserved",
        "single_step_local_ticket_duration_preserved",
        "communication_law_still_deferred_to_v61",
    ]
    if refreshed_continuation_decision.refresh_reason_codes != required_reason_codes:
        raise ValueError(
            "V60-B continuation refresh decision does not preserve the shipped reason codes"
        )
    expected_selected_path_dependencies = [
        refreshed_task_residual.refresh_packet_id,
        prior_loop_state_ledger.ledger_id,
    ]
    if (
        refreshed_continuation_decision.field_dependence_tags["selected_next_path_summary_or_none"]
        != expected_selected_path_dependencies
    ):
        raise ValueError(
            "V60-B continuation refresh decision must preserve the shipped selected-next-path "
            "dependence tags"
        )
    if refreshed_continuation_decision.field_dependence_tags[
        "reproposal_basis_summary_or_none"
    ] != ["none_under_current_v60b_policy"]:
        raise ValueError(
            "V60-B continuation refresh decision must preserve the shipped reproposal "
            "absence dependence tags"
        )


def _build_v60c_continuation_hardening_register(
    *,
    seed_intent: AgenticDeSeedIntentRecord,
    task_charter: AgenticDeTaskCharterPacket,
    task_residual: AgenticDeTaskResidualPacket,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_decision: AgenticDeContinuationDecisionRecord,
    refreshed_task_residual: AgenticDeTaskResidualRefreshPacket,
    refreshed_continuation_decision: AgenticDeContinuationRefreshDecisionRecord,
    evidence_refs: list[str],
) -> AgenticDeContinuationHardeningRegister:
    root_origin_ids = [
        f"seed:{seed_intent.seed_intent_id}",
        f"charter:{task_charter.charter_id}",
        f"residual:{task_residual.residual_id}",
        f"loop:{loop_state_ledger.ledger_id}",
        f"starter_decision:{continuation_decision.decision_id}",
        f"refresh:{refreshed_task_residual.refresh_packet_id}",
        f"refresh_decision:{refreshed_continuation_decision.refresh_decision_id}",
        f"latest_act:{refreshed_continuation_decision.latest_reintegrated_act_identity}",
        f"policy:{V60C_FROZEN_POLICY_REF}",
    ]
    field_origin_tags = {
        "starter_continuation_outcome": "prior_artifact",
        "latest_reintegrated_act_selection_basis_summary": "prior_artifact",
        "refresh_outcome": "prior_artifact",
        "selected_next_path_summary_or_none": "prior_artifact",
        "reproposal_basis_summary_or_none": "prior_artifact",
        "frozen_policy_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "verdict_basis_summary": "current_turn_derived",
        "recommended_outcome": "current_turn_derived",
    }
    field_dependence_tags = {
        "starter_continuation_outcome": [
            continuation_decision.decision_id,
            task_charter.charter_id,
            loop_state_ledger.ledger_id,
        ],
        "latest_reintegrated_act_selection_basis_summary": [
            refreshed_task_residual.refresh_packet_id,
            refreshed_continuation_decision.refresh_decision_id,
        ],
        "refresh_outcome": [
            refreshed_continuation_decision.refresh_decision_id,
            refreshed_task_residual.refresh_packet_id,
            V60B_FROZEN_POLICY_REF,
        ],
        "selected_next_path_summary_or_none": [
            refreshed_task_residual.refresh_packet_id,
            loop_state_ledger.ledger_id,
        ],
        "reproposal_basis_summary_or_none": ["none_under_current_v60c_policy"],
        "frozen_policy_ref": [],
        "evidence_basis_summary": [
            seed_intent.seed_intent_id,
            task_charter.charter_id,
            task_residual.residual_id,
            loop_state_ledger.ledger_id,
            continuation_decision.decision_id,
            refreshed_task_residual.refresh_packet_id,
            refreshed_continuation_decision.refresh_decision_id,
            V60C_FROZEN_POLICY_REF,
        ],
        "verdict_basis_summary": [
            continuation_decision.decision_id,
            refreshed_continuation_decision.refresh_decision_id,
            *root_origin_ids,
        ],
        "recommended_outcome": [
            continuation_decision.decision_id,
            refreshed_continuation_decision.refresh_decision_id,
            V60C_FROZEN_POLICY_REF,
        ],
    }
    entry = AgenticDeContinuationHardeningEntry(
        seed_intent_ref=seed_intent.seed_intent_id,
        task_charter_ref=task_charter.charter_id,
        task_residual_ref=task_residual.residual_id,
        loop_state_ledger_ref=loop_state_ledger.ledger_id,
        continuation_decision_ref=continuation_decision.decision_id,
        task_residual_refresh_ref=refreshed_task_residual.refresh_packet_id,
        continuation_refresh_decision_ref=refreshed_continuation_decision.refresh_decision_id,
        starter_continuation_outcome=continuation_decision.continuation_outcome,
        latest_reintegrated_act_identity=refreshed_task_residual.latest_reintegrated_act_identity,
        latest_reintegrated_act_selection_basis_summary=(
            refreshed_task_residual.latest_reintegrated_act_selection_basis_summary
        ),
        refresh_outcome=refreshed_continuation_decision.refresh_outcome,
        selected_next_path_summary_or_none=(
            refreshed_continuation_decision.selected_next_path_summary_or_none
        ),
        reproposal_basis_summary_or_none=(
            refreshed_continuation_decision.reproposal_basis_summary_or_none
        ),
        selected_hardening_target_surface=(
            "shipped_v60a_v60b_continuation_lineage_over_continuity_bound_create_new_exemplar_only"
        ),
        frozen_policy_ref=V60C_FROZEN_POLICY_REF,
        evidence_basis_summary=(
            "shipped V60-A seed intent/charter/residual/loop/continuation decision plus "
            "shipped V60-B residual refresh/continuation refresh over the same exact "
            "continuity-bound create_new exemplar"
        ),
        verdict_basis_summary=(
            "starter continuation remained continue_to_governed_act, one explicit latest "
            "reintegrated act identity remained selected by shipped V60-B basis, refresh "
            "continuation remained continue_to_governed_act, reproposal stayed absent, "
            "the exact selected downstream path stayed preserved, and provenance/dedup "
            "remained explicit under one frozen V60-C policy anchor"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated continuation-lineage artifacts remain non-independent advisory support"
        ),
        recommended_outcome="candidate_for_later_continuation_hardening",
        rationale=(
            "the exact shipped V60-A/V60-B continuation lineage now has typed seed "
            "ingress, replayable charter compilation, derived non-authorizing residual "
            "carriage, stable loop identity, explicit latest-act selection, and replayable "
            "refresh posture under frozen policy, so it is a valid later path-level "
            "continuation hardening candidate, but any broader continuation, migration, "
            "communication, or autonomy scope still requires a later explicit lock"
        ),
        reason_codes=[
            "starter_continue_to_governed_act",
            "refresh_continue_to_governed_act",
            "latest_reintegrated_act_selected_explicitly",
            "exact_selected_downstream_path_preserved",
            "path_level_only",
            "extensional_replayable_policy",
            "lineage_root_dedup_applied",
            "candidate_non_entitling_and_non_escalating",
            "later_lock_required_for_scope",
            "no_live_mutation_in_v60c",
            "non_generalizing_by_default",
        ],
        evidence_refs=evidence_refs,
    )
    return AgenticDeContinuationHardeningRegister(
        target_arc=V60C_TARGET_ARC,
        target_path=V60C_TARGET_PATH,
        baseline_checker_version=V60B_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


def run_agentic_de_continuation_v60c(
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
    v60a_lane_drift_path: Path = DEFAULT_V60A_LANE_DRIFT_PATH,
    v60a_seed_intent_path: Path = DEFAULT_V60A_SEED_INTENT_PATH,
    v60a_task_charter_path: Path = DEFAULT_V60A_TASK_CHARTER_PATH,
    v60a_task_residual_path: Path = DEFAULT_V60A_TASK_RESIDUAL_PATH,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60a_continuation_decision_path: Path = DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    v60b_lane_drift_path: Path = DEFAULT_V60B_LANE_DRIFT_PATH,
    v60b_task_residual_refresh_path: Path = DEFAULT_V60B_TASK_RESIDUAL_REFRESH_PATH,
    v60b_continuation_refresh_decision_path: Path = (
        DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH
    ),
    lane_drift_path: Path = DEFAULT_V60C_LANE_DRIFT_PATH,
    v59a_evidence_path: Path = DEFAULT_V59A_EVIDENCE_PATH,
    v59b_evidence_path: Path = DEFAULT_V59B_EVIDENCE_PATH,
    v60a_evidence_path: Path = DEFAULT_V60A_EVIDENCE_PATH,
    v60b_evidence_path: Path = DEFAULT_V60B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeContinuationHardeningRegister:
    root_raw = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if root_raw.exists() and root_raw.is_symlink():
        raise ValueError("repository root may not be a symlink for V60-C continuation")
    root = root_raw.resolve()

    path_fields = (
        "domain_packet_path",
        "morph_ir_path",
        "interaction_contract_path",
        "action_proposal_path",
        "v56a_checkpoint_path",
        "v56a_diagnostics_path",
        "v56a_conformance_path",
        "v56b_lane_drift_path",
        "v56b_action_class_taxonomy_path",
        "v56b_runtime_state_path",
        "v56b_action_ticket_path",
        "v56b_diagnostics_path",
        "v56b_conformance_path",
        "v56c_lane_drift_path",
        "v56c_runtime_harvest_path",
        "v56c_governance_calibration_path",
        "v56c_migration_decision_path",
        "v59a_lane_drift_path",
        "v59a_continuity_region_path",
        "v59a_continuity_admission_path",
        "v59a_occupancy_path",
        "v59a_live_turn_admission_path",
        "v59a_live_turn_handoff_path",
        "v59a_observation_path",
        "v59a_local_effect_conformance_path",
        "v59a_live_turn_reintegration_path",
        "v59a_continuity_reintegration_path",
        "v59b_lane_drift_path",
        "v59b_continuity_restoration_handoff_path",
        "v59b_restoration_path",
        "v59b_continuity_restoration_reintegration_path",
        "v60a_lane_drift_path",
        "v60a_seed_intent_path",
        "v60a_task_charter_path",
        "v60a_task_residual_path",
        "v60a_loop_state_ledger_path",
        "v60a_continuation_decision_path",
        "v60b_lane_drift_path",
        "v60b_task_residual_refresh_path",
        "v60b_continuation_refresh_decision_path",
        "lane_drift_path",
        "v59a_evidence_path",
        "v59b_evidence_path",
        "v60a_evidence_path",
        "v60b_evidence_path",
    )
    locals_map = locals()
    resolved_paths: dict[str, Path] = {}
    for field_name in path_fields:
        candidate = _resolve_path(repo_root_path=root, path=locals_map[field_name])
        _assert_v60c_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v60c_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v60b_lane_drift_record(load_lane_drift_record(resolved_paths["v60b_lane_drift_path"]))
    _validate_v60a_lane_drift_record(load_lane_drift_record(resolved_paths["v60a_lane_drift_path"]))
    _validate_v59b_lane_drift_record(load_lane_drift_record(resolved_paths["v59b_lane_drift_path"]))
    _validate_v59a_lane_drift_record(load_lane_drift_record(resolved_paths["v59a_lane_drift_path"]))
    _validate_v56b_lane_drift_record(load_lane_drift_record(resolved_paths["v56b_lane_drift_path"]))
    _validate_v56c_lane_drift_record(load_lane_drift_record(resolved_paths["v56c_lane_drift_path"]))
    _validate_v59a_evidence_payload(
        _load_json_object(resolved_paths["v59a_evidence_path"], error_label="V59-A evidence")
    )
    _validate_v59b_evidence_payload(
        _load_json_object(resolved_paths["v59b_evidence_path"], error_label="V59-B evidence")
    )
    _validate_v60a_evidence_payload(
        _load_json_object(resolved_paths["v60a_evidence_path"], error_label="V60-A evidence")
    )
    _validate_v60b_evidence_payload(
        _load_json_object(resolved_paths["v60b_evidence_path"], error_label="V60-B evidence")
    )

    packet = load_domain_packet(resolved_paths["domain_packet_path"])
    morph_ir = load_morph_ir(resolved_paths["morph_ir_path"])
    contract = load_interaction_contract(resolved_paths["interaction_contract_path"])
    proposal = load_action_proposal(resolved_paths["action_proposal_path"])
    v56a_checkpoint = load_membrane_checkpoint(resolved_paths["v56a_checkpoint_path"])
    v56a_diagnostics = load_morph_diagnostics(resolved_paths["v56a_diagnostics_path"])
    v56a_conformance = load_conformance_report(resolved_paths["v56a_conformance_path"])
    v56b_taxonomy = load_action_class_taxonomy(resolved_paths["v56b_action_class_taxonomy_path"])
    v56b_runtime_state = load_runtime_state(resolved_paths["v56b_runtime_state_path"])
    v56b_ticket = load_action_ticket(resolved_paths["v56b_action_ticket_path"])
    v56b_diagnostics = load_morph_diagnostics(resolved_paths["v56b_diagnostics_path"])
    v56b_conformance = load_conformance_report(resolved_paths["v56b_conformance_path"])
    v56c_harvest = load_runtime_harvest_record(resolved_paths["v56c_runtime_harvest_path"])
    v56c_governance = load_governance_calibration_register(
        resolved_paths["v56c_governance_calibration_path"]
    )
    v56c_migration = load_migration_decision_register(
        resolved_paths["v56c_migration_decision_path"]
    )
    v59a_continuity_region = load_workspace_continuity_region_declaration(
        resolved_paths["v59a_continuity_region_path"]
    )
    v59a_continuity_admission = load_workspace_continuity_admission_record(
        resolved_paths["v59a_continuity_admission_path"]
    )
    v59a_occupancy = load_workspace_occupancy_report(resolved_paths["v59a_occupancy_path"])
    v59a_live_turn_admission = load_live_turn_admission_record(
        resolved_paths["v59a_live_turn_admission_path"]
    )
    v59a_live_turn_handoff = load_live_turn_handoff_record(
        resolved_paths["v59a_live_turn_handoff_path"]
    )
    v59a_observation = load_local_effect_observation_record(resolved_paths["v59a_observation_path"])
    v59a_conformance = load_local_effect_conformance_report(
        resolved_paths["v59a_local_effect_conformance_path"]
    )
    v59a_live_turn_reintegration = load_live_turn_reintegration_report(
        resolved_paths["v59a_live_turn_reintegration_path"]
    )
    v59a_continuity_reintegration = load_workspace_continuity_reintegration_report(
        resolved_paths["v59a_continuity_reintegration_path"]
    )
    v59b_continuity_restoration_handoff = load_workspace_continuity_restoration_handoff_record(
        resolved_paths["v59b_continuity_restoration_handoff_path"]
    )
    v59b_restoration = load_local_effect_restoration_record(resolved_paths["v59b_restoration_path"])
    v59b_continuity_restoration_reintegration = (
        load_workspace_continuity_restoration_reintegration_report(
            resolved_paths["v59b_continuity_restoration_reintegration_path"]
        )
    )
    v60a_seed_intent = load_seed_intent_record(resolved_paths["v60a_seed_intent_path"])
    v60a_task_charter = load_task_charter_packet(resolved_paths["v60a_task_charter_path"])
    v60a_task_residual = load_task_residual_packet(resolved_paths["v60a_task_residual_path"])
    v60a_loop_state_ledger = load_loop_state_ledger(resolved_paths["v60a_loop_state_ledger_path"])
    v60a_continuation_decision = load_continuation_decision_record(
        resolved_paths["v60a_continuation_decision_path"]
    )
    v60b_task_residual_refresh = load_task_residual_refresh_packet(
        resolved_paths["v60b_task_residual_refresh_path"]
    )
    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
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
    _validate_v60a_continuation_surfaces(
        seed_intent=v60a_seed_intent,
        task_charter=v60a_task_charter,
        task_residual=v60a_task_residual,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_decision=v60a_continuation_decision,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        target_relative_path=target_relative_path,
    )
    _validate_v60b_refresh_surfaces(
        prior_task_charter=v60a_task_charter,
        prior_task_residual=v60a_task_residual,
        prior_loop_state_ledger=v60a_loop_state_ledger,
        prior_continuation_decision=v60a_continuation_decision,
        refreshed_task_residual=v60b_task_residual_refresh,
        refreshed_continuation_decision=v60b_continuation_refresh_decision,
        latest_live_turn_reintegration=v59a_live_turn_reintegration,
        latest_continuity_reintegration=v59a_continuity_reintegration,
        latest_continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=resolved_paths["domain_packet_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["morph_ir_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["interaction_contract_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["action_proposal_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56a_checkpoint_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56a_diagnostics_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56a_conformance_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v56b_action_class_taxonomy_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56b_runtime_state_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56b_action_ticket_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56b_lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56b_diagnostics_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56b_conformance_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56c_lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56c_runtime_harvest_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v56c_governance_calibration_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v56c_migration_decision_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_continuity_region_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_continuity_admission_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_occupancy_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_live_turn_admission_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_live_turn_handoff_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_observation_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_local_effect_conformance_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_live_turn_reintegration_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_continuity_reintegration_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59b_lane_drift_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v59b_continuity_restoration_handoff_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59b_restoration_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v59b_continuity_restoration_reintegration_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_seed_intent_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_charter_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_residual_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_loop_state_ledger_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v60a_continuation_decision_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60b_lane_drift_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v60b_task_residual_refresh_path"]
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59b_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60b_evidence_path"]),
    ]
    return _build_v60c_continuation_hardening_register(
        seed_intent=v60a_seed_intent,
        task_charter=v60a_task_charter,
        task_residual=v60a_task_residual,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_decision=v60a_continuation_decision,
        refreshed_task_residual=v60b_task_residual_refresh,
        refreshed_continuation_decision=v60b_continuation_refresh_decision,
        evidence_refs=evidence_refs,
    )


def _validate_v61a_send_request(
    *,
    request: CopilotSessionSendRequest,
    expected_session_id: str,
) -> str:
    if request.provider != "codex":
        raise ValueError("V61-A requires the codex provider on the selected send seam")
    if request.session_id != expected_session_id:
        raise ValueError("V61-A send request must bind the shipped V60 resident session")
    message = request.message
    method = message.get("method") if isinstance(message, dict) else None
    if method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V61-A starter seam requires copilot.user_message only")
    params = message.get("params") if isinstance(message, dict) else None
    text = params.get("text") if isinstance(params, dict) else None
    if not isinstance(text, str) or not text.strip():
        raise ValueError("V61-A send request requires non-empty params.text")
    return text.strip()


def _validate_v61a_v60c_hardening_register(
    register: AgenticDeContinuationHardeningRegister,
    *,
    continuation_decision: AgenticDeContinuationDecisionRecord,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
) -> None:
    if register.target_arc != V60C_TARGET_ARC or register.target_path != V60C_TARGET_PATH:
        raise ValueError("V61-A requires the shipped V60-C continuation hardening surface")
    if register.baseline_checker_version != V60B_CHECKER_VERSION:
        raise ValueError("V61-A requires the shipped V60-B baseline checker version")
    if register.entry_count != 1:
        raise ValueError("V61-A requires one shipped V60-C hardening entry only")
    entry = register.entries[0]
    if entry.continuation_decision_ref != continuation_decision.decision_id:
        raise ValueError("V61-A requires the shipped V60-C starter continuation basis")
    if entry.continuation_refresh_decision_ref != continuation_refresh_decision.refresh_decision_id:
        raise ValueError("V61-A requires the shipped V60-C refresh continuation basis")
    if entry.recommended_outcome != "candidate_for_later_continuation_hardening":
        raise ValueError("V61-A requires the shipped non-live V60-C advisory posture")


def _select_v61a_interpretation_posture(message_text: str) -> str:
    normalized = message_text.lower()
    if "charter" in normalized or "scope" in normalized or "change target" in normalized:
        return "charter_amendment_candidate"
    if "status" in normalized:
        return "status_request"
    if "authority" in normalized or "approve" in normalized:
        return "authority_response"
    if "clarify" in normalized or "?" in message_text:
        return "clarification_response"
    return "advisory_only_message"


def _select_v61a_egress_posture(interpretation_posture: str) -> str:
    if interpretation_posture == "status_request":
        return "status_update"
    if interpretation_posture == "authority_response":
        return "authority_request"
    if interpretation_posture == "clarification_response":
        return "clarification_question"
    if interpretation_posture == "charter_amendment_candidate":
        return "advisory_only_message"
    return "advisory_only_message"


def _build_v61a_communication_ingress_packet(
    *,
    send_request: CopilotSessionSendRequest,
    message_text: str,
    task_charter: AgenticDeTaskCharterPacket,
    refreshed_continuation_decision: AgenticDeContinuationRefreshDecisionRecord,
    evidence_refs: list[str],
) -> AgenticDeCommunicationIngressPacket:
    field_origin_tags = {
        "source_principal_class": "current_turn_native",
        "speaker_class": "current_turn_native",
        "surface_class": "current_turn_derived",
        "surface_instance_or_session_identity": "current_turn_native",
        "selected_runtime_message_method": "current_turn_native",
        "ingress_payload_summary": "current_turn_derived",
        "seed_or_continuation_basis_summary": "prior_artifact",
        "ingress_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "source_principal_class": [],
        "speaker_class": [],
        "surface_class": [V61A_SELECTED_API_ROUTE],
        "surface_instance_or_session_identity": [send_request.session_id],
        "selected_runtime_message_method": [V61A_SELECTED_RUNTIME_METHOD],
        "ingress_payload_summary": [send_request.client_request_id, send_request.session_id],
        "seed_or_continuation_basis_summary": [
            task_charter.charter_id,
            refreshed_continuation_decision.refresh_decision_id,
        ],
        "ingress_basis_summary": [
            send_request.client_request_id,
            send_request.session_id,
            refreshed_continuation_decision.refresh_decision_id,
        ],
    }
    root_origin_ids = [
        f"session:{send_request.session_id}",
        f"request:{send_request.client_request_id}",
        f"charter:{task_charter.charter_id}",
        f"refresh:{refreshed_continuation_decision.refresh_decision_id}",
    ]
    return AgenticDeCommunicationIngressPacket(
        target_arc=V61A_TARGET_ARC,
        target_path=V61A_TARGET_PATH,
        resident_session_ref=send_request.session_id,
        source_principal_class=V61A_SELECTED_SOURCE_PRINCIPAL_CLASS,
        speaker_class=V61A_SELECTED_SPEAKER_CLASS,
        surface_class=V61A_SELECTED_SURFACE_CLASS,
        surface_instance_or_session_identity=send_request.session_id,
        selected_api_route_ref_or_equivalent=V61A_SELECTED_API_ROUTE,
        selected_runtime_message_method=V61A_SELECTED_RUNTIME_METHOD,
        ingress_payload_summary=(
            f"copilot.user_message over resident send seam with {len(message_text)} chars"
        ),
        seed_or_continuation_basis_summary=(
            "latest shipped V60 continuation basis remains the exact V60-B refresh decision "
            "over the continuity-bound create_new exemplar"
        ),
        ingress_basis_summary=(
            "resident /urm/copilot/send seam + typed user message payload + shipped V60 "
            "continuation basis only"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=evidence_refs,
    )


def _build_v61a_surface_authority_descriptor(
    *,
    ingress: AgenticDeCommunicationIngressPacket,
    evidence_refs: list[str],
) -> AgenticDeSurfaceAuthorityDescriptor:
    field_origin_tags = {
        "surface_class": "current_turn_derived",
        "surface_affordance_classes": "current_turn_derived",
        "bounded_authority_posture_summary": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
        "descriptor_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "surface_class": [ingress.communication_ingress_id],
        "surface_affordance_classes": [ingress.communication_ingress_id, V61A_FROZEN_POLICY_REF],
        "bounded_authority_posture_summary": [
            ingress.communication_ingress_id,
            V61A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [],
        "descriptor_basis_summary": [ingress.communication_ingress_id, V61A_FROZEN_POLICY_REF],
    }
    return AgenticDeSurfaceAuthorityDescriptor(
        target_arc=V61A_TARGET_ARC,
        target_path=V61A_TARGET_PATH,
        communication_ingress_ref=ingress.communication_ingress_id,
        surface_class=V61A_SELECTED_SURFACE_CLASS,
        surface_instance_or_session_identity=ingress.surface_instance_or_session_identity,
        surface_affordance_classes=["communication", "advisory", "authority_request"],
        bounded_authority_posture_summary=(
            "resident send seam carries typed communication posture only; not bridge office, "
            "not execute, not native witness"
        ),
        frozen_policy_anchor_ref=V61A_FROZEN_POLICY_REF,
        descriptor_basis_summary=(
            "same selected resident send seam facts plus same frozen V61-A policy yield the "
            "same surface descriptor"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=[
            *ingress.root_origin_ids,
            f"policy:{V61A_FROZEN_POLICY_REF}",
        ],
        evidence_refs=[ingress.communication_ingress_id, *evidence_refs],
    )


def _build_v61a_ingress_interpretation_record(
    *,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    task_charter: AgenticDeTaskCharterPacket,
    loop_state_ledger: AgenticDeLoopStateLedger,
    latest_v60_continuation_basis_ref: str,
    interpretation_posture: str,
    evidence_refs: list[str],
) -> AgenticDeIngressInterpretationRecord:
    field_origin_tags = {
        "interpretation_posture": "current_turn_derived",
        "latest_v60_continuation_basis_selection_summary": "prior_artifact",
        "frozen_policy_anchor_ref": "shaping_only",
        "interpretation_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "interpretation_posture": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            latest_v60_continuation_basis_ref,
            V61A_FROZEN_POLICY_REF,
        ],
        "latest_v60_continuation_basis_selection_summary": [latest_v60_continuation_basis_ref],
        "frozen_policy_anchor_ref": [],
        "interpretation_basis_summary": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            task_charter.charter_id,
            loop_state_ledger.ledger_id,
            latest_v60_continuation_basis_ref,
            V61A_FROZEN_POLICY_REF,
        ],
    }
    reason_codes = [
        f"interpreted_{interpretation_posture}",
        "surface_descriptor_not_message_interpretation",
        "charter_mutation_not_selected_in_v61a",
    ]
    return AgenticDeIngressInterpretationRecord(
        target_arc=V61A_TARGET_ARC,
        target_path=V61A_TARGET_PATH,
        communication_ingress_ref=ingress.communication_ingress_id,
        surface_authority_descriptor_ref=descriptor.surface_authority_descriptor_id,
        task_charter_ref=task_charter.charter_id,
        loop_state_ledger_ref=loop_state_ledger.ledger_id,
        latest_v60_continuation_basis_ref=latest_v60_continuation_basis_ref,
        latest_v60_continuation_basis_selection_summary=(
            "latest shipped V60-B refresh decision selected as current continuation basis "
            "because V60-B closed on main and preserves exact downstream path"
        ),
        frozen_policy_anchor_ref=V61A_FROZEN_POLICY_REF,
        interpretation_posture=interpretation_posture,
        interpretation_reason_codes=reason_codes,
        interpretation_basis_summary=(
            "typed ingress packet + surface descriptor + shipped V60 charter/loop/refresh "
            "basis + frozen V61-A policy anchor"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=[
            *descriptor.root_origin_ids,
            f"basis:{latest_v60_continuation_basis_ref}",
        ],
        evidence_refs=[
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            task_charter.charter_id,
            loop_state_ledger.ledger_id,
            latest_v60_continuation_basis_ref,
            *evidence_refs,
        ],
    )


def _build_v61a_communication_egress_packet(
    *,
    interpretation: AgenticDeIngressInterpretationRecord,
    task_charter: AgenticDeTaskCharterPacket,
    latest_v60_continuation_basis_ref: str,
    egress_posture: str,
    evidence_refs: list[str],
) -> AgenticDeCommunicationEgressPacket:
    field_origin_tags = {
        "selected_egress_posture": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
        "egress_basis_summary": "current_turn_derived",
        "egress_payload_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "selected_egress_posture": [
            interpretation.ingress_interpretation_id,
            latest_v60_continuation_basis_ref,
            V61A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [],
        "egress_basis_summary": [
            interpretation.ingress_interpretation_id,
            task_charter.charter_id,
            latest_v60_continuation_basis_ref,
            V61A_FROZEN_POLICY_REF,
        ],
        "egress_payload_summary": [
            interpretation.ingress_interpretation_id,
            latest_v60_continuation_basis_ref,
        ],
    }
    return AgenticDeCommunicationEgressPacket(
        target_arc=V61A_TARGET_ARC,
        target_path=V61A_TARGET_PATH,
        ingress_interpretation_ref=interpretation.ingress_interpretation_id,
        task_charter_ref=task_charter.charter_id,
        latest_v60_continuation_basis_ref=latest_v60_continuation_basis_ref,
        selected_egress_posture=egress_posture,
        selected_egress_surface_ref=V61A_SELECTED_API_ROUTE,
        egress_payload_summary=(
            f"typed governed communication egress over resident send seam as {egress_posture}"
        ),
        frozen_policy_anchor_ref=V61A_FROZEN_POLICY_REF,
        egress_basis_summary=(
            "typed ingress interpretation + latest shipped V60 continuation basis + frozen "
            "V61-A policy anchor"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=[
            *interpretation.root_origin_ids,
            f"egress:{egress_posture}",
        ],
        evidence_refs=[
            interpretation.ingress_interpretation_id,
            task_charter.charter_id,
            latest_v60_continuation_basis_ref,
            *evidence_refs,
        ],
    )


def run_agentic_de_governed_communication_v61a(
    *,
    repo_root_path: Path | None = None,
    v59a_live_turn_reintegration_path: Path = DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    v59a_continuity_reintegration_path: Path = DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    v59b_continuity_restoration_reintegration_path: Path = (
        DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH
    ),
    v60a_lane_drift_path: Path = DEFAULT_V60A_LANE_DRIFT_PATH,
    v60a_seed_intent_path: Path = DEFAULT_V60A_SEED_INTENT_PATH,
    v60a_task_charter_path: Path = DEFAULT_V60A_TASK_CHARTER_PATH,
    v60a_task_residual_path: Path = DEFAULT_V60A_TASK_RESIDUAL_PATH,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60a_continuation_decision_path: Path = DEFAULT_V60A_CONTINUATION_DECISION_PATH,
    v60b_lane_drift_path: Path = DEFAULT_V60B_LANE_DRIFT_PATH,
    v60b_task_residual_refresh_path: Path = DEFAULT_V60B_TASK_RESIDUAL_REFRESH_PATH,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v60c_lane_drift_path: Path = DEFAULT_V60C_LANE_DRIFT_PATH,
    v60c_hardening_path: Path = DEFAULT_V60C_HARDENING_PATH,
    lane_drift_path: Path = DEFAULT_V61A_LANE_DRIFT_PATH,
    send_request_path: Path = DEFAULT_V61A_SEND_REQUEST_PATH,
    v60a_evidence_path: Path = DEFAULT_V60A_EVIDENCE_PATH,
    v60b_evidence_path: Path = DEFAULT_V60B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> tuple[
    AgenticDeCommunicationIngressPacket,
    AgenticDeSurfaceAuthorityDescriptor,
    AgenticDeIngressInterpretationRecord,
    AgenticDeCommunicationEgressPacket,
]:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V61-A communication")
    root = raw_root.resolve()

    path_args = {
        "v59a_live_turn_reintegration_path": v59a_live_turn_reintegration_path,
        "v59a_continuity_reintegration_path": v59a_continuity_reintegration_path,
        "v59b_continuity_restoration_reintegration_path": (
            v59b_continuity_restoration_reintegration_path
        ),
        "v60a_lane_drift_path": v60a_lane_drift_path,
        "v60a_seed_intent_path": v60a_seed_intent_path,
        "v60a_task_charter_path": v60a_task_charter_path,
        "v60a_task_residual_path": v60a_task_residual_path,
        "v60a_loop_state_ledger_path": v60a_loop_state_ledger_path,
        "v60a_continuation_decision_path": v60a_continuation_decision_path,
        "v60b_lane_drift_path": v60b_lane_drift_path,
        "v60b_task_residual_refresh_path": v60b_task_residual_refresh_path,
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v60c_lane_drift_path": v60c_lane_drift_path,
        "v60c_hardening_path": v60c_hardening_path,
        "lane_drift_path": lane_drift_path,
        "send_request_path": send_request_path,
        "v60a_evidence_path": v60a_evidence_path,
        "v60b_evidence_path": v60b_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v61a_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v61a_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v60c_lane_drift_record(load_lane_drift_record(resolved_paths["v60c_lane_drift_path"]))
    _validate_v60b_lane_drift_record(load_lane_drift_record(resolved_paths["v60b_lane_drift_path"]))
    _validate_v60a_lane_drift_record(load_lane_drift_record(resolved_paths["v60a_lane_drift_path"]))
    _validate_v60a_evidence_payload(
        _load_json_object(resolved_paths["v60a_evidence_path"], error_label="V60-A evidence")
    )
    _validate_v60b_evidence_payload(
        _load_json_object(resolved_paths["v60b_evidence_path"], error_label="V60-B evidence")
    )

    v59a_live_turn_reintegration = load_live_turn_reintegration_report(
        resolved_paths["v59a_live_turn_reintegration_path"]
    )
    v59a_continuity_reintegration = load_workspace_continuity_reintegration_report(
        resolved_paths["v59a_continuity_reintegration_path"]
    )
    v59b_continuity_restoration_reintegration = (
        load_workspace_continuity_restoration_reintegration_report(
            resolved_paths["v59b_continuity_restoration_reintegration_path"]
        )
    )
    v60a_seed_intent = load_seed_intent_record(resolved_paths["v60a_seed_intent_path"])
    v60a_task_charter = load_task_charter_packet(resolved_paths["v60a_task_charter_path"])
    v60a_task_residual = load_task_residual_packet(resolved_paths["v60a_task_residual_path"])
    v60a_loop_state_ledger = load_loop_state_ledger(resolved_paths["v60a_loop_state_ledger_path"])
    v60a_continuation_decision = load_continuation_decision_record(
        resolved_paths["v60a_continuation_decision_path"]
    )
    v60b_task_residual_refresh = load_task_residual_refresh_packet(
        resolved_paths["v60b_task_residual_refresh_path"]
    )
    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v60c_hardening = load_continuation_hardening_register(resolved_paths["v60c_hardening_path"])
    send_request = load_copilot_session_send_request(resolved_paths["send_request_path"])

    _validate_v60a_continuation_surfaces(
        seed_intent=v60a_seed_intent,
        task_charter=v60a_task_charter,
        task_residual=v60a_task_residual,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_decision=v60a_continuation_decision,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        target_relative_path=target_relative_path,
    )
    _validate_v60b_refresh_surfaces(
        prior_task_charter=v60a_task_charter,
        prior_task_residual=v60a_task_residual,
        prior_loop_state_ledger=v60a_loop_state_ledger,
        prior_continuation_decision=v60a_continuation_decision,
        refreshed_task_residual=v60b_task_residual_refresh,
        refreshed_continuation_decision=v60b_continuation_refresh_decision,
        latest_live_turn_reintegration=v59a_live_turn_reintegration,
        latest_continuity_reintegration=v59a_continuity_reintegration,
        latest_continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        target_relative_path=target_relative_path,
    )
    _validate_v61a_v60c_hardening_register(
        v60c_hardening,
        continuation_decision=v60a_continuation_decision,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
    )
    message_text = _validate_v61a_send_request(
        request=send_request,
        expected_session_id=v60a_loop_state_ledger.resident_session_ref,
    )

    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if v60b_continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V61-A requires the shipped exact downstream V60 selected path")

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v59a_live_turn_reintegration_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v59a_continuity_reintegration_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v59b_continuity_restoration_reintegration_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_seed_intent_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_charter_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_residual_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60a_loop_state_ledger_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60a_continuation_decision_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60b_lane_drift_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_task_residual_refresh_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60c_lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60c_hardening_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["send_request_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60b_evidence_path"]),
    ]

    latest_v60_continuation_basis_ref = v60b_continuation_refresh_decision.refresh_decision_id
    ingress = _build_v61a_communication_ingress_packet(
        send_request=send_request,
        message_text=message_text,
        task_charter=v60a_task_charter,
        refreshed_continuation_decision=v60b_continuation_refresh_decision,
        evidence_refs=evidence_refs,
    )
    descriptor = _build_v61a_surface_authority_descriptor(
        ingress=ingress,
        evidence_refs=evidence_refs,
    )
    interpretation_posture = _select_v61a_interpretation_posture(message_text)
    interpretation = _build_v61a_ingress_interpretation_record(
        ingress=ingress,
        descriptor=descriptor,
        task_charter=v60a_task_charter,
        loop_state_ledger=v60a_loop_state_ledger,
        latest_v60_continuation_basis_ref=latest_v60_continuation_basis_ref,
        interpretation_posture=interpretation_posture,
        evidence_refs=evidence_refs,
    )
    egress = _build_v61a_communication_egress_packet(
        interpretation=interpretation,
        task_charter=v60a_task_charter,
        latest_v60_continuation_basis_ref=latest_v60_continuation_basis_ref,
        egress_posture=_select_v61a_egress_posture(interpretation_posture),
        evidence_refs=evidence_refs,
    )
    return ingress, descriptor, interpretation, egress


def _validate_v61b_v61a_surfaces(
    *,
    task_charter: AgenticDeTaskCharterPacket,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    egress: AgenticDeCommunicationEgressPacket,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V61-B requires the shipped exact downstream V60 selected path")
    if ingress.target_arc != V61A_TARGET_ARC or ingress.target_path != V61A_TARGET_PATH:
        raise ValueError("V61-B requires the shipped V61-A communication ingress surface")
    if descriptor.target_arc != V61A_TARGET_ARC or descriptor.target_path != V61A_TARGET_PATH:
        raise ValueError("V61-B requires the shipped V61-A surface authority descriptor")
    if (
        interpretation.target_arc != V61A_TARGET_ARC
        or interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V61-B requires the shipped V61-A ingress interpretation surface")
    if egress.target_arc != V61A_TARGET_ARC or egress.target_path != V61A_TARGET_PATH:
        raise ValueError("V61-B requires the shipped V61-A communication egress surface")
    if ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V61-B requires the shipped exact resident V61-A API route")
    if ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V61-B requires the shipped exact resident V61-A runtime method")
    if ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V61-B requires the shipped exact resident V61-A surface class")
    if descriptor.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V61-B descriptor must bind the shipped V61-A ingress packet")
    if interpretation.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V61-B interpretation must bind the shipped V61-A ingress packet")
    if (
        interpretation.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V61-B interpretation must bind the shipped V61-A descriptor")
    if interpretation.task_charter_ref != task_charter.charter_id:
        raise ValueError("V61-B interpretation must bind the shipped V60 task charter")
    if interpretation.loop_state_ledger_ref != loop_state_ledger.ledger_id:
        raise ValueError("V61-B interpretation must bind the shipped V60 loop-state ledger")
    if (
        interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V61-B interpretation must bind the shipped V60-B refresh decision")
    if egress.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V61-B egress must bind the shipped V61-A interpretation")
    if egress.task_charter_ref != task_charter.charter_id:
        raise ValueError("V61-B egress must bind the shipped V60 task charter")
    if (
        egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V61-B egress must bind the shipped V60-B refresh decision")
    if egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V61-B requires the shipped exact resident V61-A egress seam")
    if ingress.resident_session_ref != loop_state_ledger.resident_session_ref:
        raise ValueError("V61-B requires the shipped V61-A resident session identity")


def _select_v61b_bridge_office_posture(
    *,
    ingress: AgenticDeCommunicationIngressPacket,
    egress: AgenticDeCommunicationEgressPacket,
) -> str:
    if (
        ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE
        or egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE
    ):
        return "resident_bridge_escalate_for_review"
    return "resident_bridge_bound"


def _select_v61b_rewitness_outcome(
    *,
    bridge_posture: str,
    egress_posture: str,
) -> str:
    if bridge_posture != "resident_bridge_bound":
        return "withheld_by_policy"
    if egress_posture in {"status_update", "completion_report", "escalation_notice"}:
        return "witness_candidate_promoted"
    return "remain_communication_only"


def _build_v61b_bridge_office_binding_record(
    *,
    task_charter: AgenticDeTaskCharterPacket,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    egress: AgenticDeCommunicationEgressPacket,
    evidence_refs: list[str],
) -> AgenticDeBridgeOfficeBindingRecord:
    selected_bridge_office_posture = _select_v61b_bridge_office_posture(
        ingress=ingress,
        egress=egress,
    )
    field_origin_tags = {
        "selected_bridge_office_posture": "current_turn_derived",
        "latest_continuation_basis_selection_summary": "prior_artifact",
        "frozen_policy_anchor_ref": "shaping_only",
        "bridge_binding_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "selected_bridge_office_posture": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            continuation_refresh_decision.refresh_decision_id,
            V61B_FROZEN_POLICY_REF,
        ],
        "latest_continuation_basis_selection_summary": [
            continuation_refresh_decision.refresh_decision_id
        ],
        "frozen_policy_anchor_ref": [],
        "bridge_binding_basis_summary": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            V61B_FROZEN_POLICY_REF,
        ],
    }
    return AgenticDeBridgeOfficeBindingRecord(
        target_arc=V61B_TARGET_ARC,
        target_path=V61B_TARGET_PATH,
        communication_ingress_ref=ingress.communication_ingress_id,
        surface_authority_descriptor_ref=descriptor.surface_authority_descriptor_id,
        ingress_interpretation_ref=interpretation.ingress_interpretation_id,
        communication_egress_ref=egress.communication_egress_id,
        task_charter_ref=task_charter.charter_id,
        latest_continuation_basis_ref=continuation_refresh_decision.refresh_decision_id,
        latest_continuation_basis_selection_summary=(
            "latest shipped V60-B refresh decision remains the selected continuation basis "
            "for explicit resident bridge-office binding over the exact V61-A seam"
        ),
        resident_session_ref=ingress.resident_session_ref,
        source_principal_class=ingress.source_principal_class,
        speaker_class=ingress.speaker_class,
        surface_instance_or_session_identity=ingress.surface_instance_or_session_identity,
        selected_bridge_office_posture=selected_bridge_office_posture,
        bridge_reason_codes=[
            f"bridge_posture_{selected_bridge_office_posture}",
            "same_bridge_facts_same_policy_same_bridge_posture",
        ],
        frozen_policy_anchor_ref=V61B_FROZEN_POLICY_REF,
        bridge_binding_basis_summary=(
            "shipped V61-A communication lineage + shipped V60 continuation basis + frozen "
            "V61-B policy anchor"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=[
            *egress.root_origin_ids,
            f"policy:{V61B_FROZEN_POLICY_REF}",
        ],
        evidence_refs=[
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            continuation_refresh_decision.refresh_decision_id,
            *evidence_refs,
        ],
    )


def _build_v61b_message_rewitness_gate_record(
    *,
    task_charter: AgenticDeTaskCharterPacket,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    interpretation: AgenticDeIngressInterpretationRecord,
    egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    evidence_refs: list[str],
) -> AgenticDeMessageRewitnessGateRecord:
    rewitness_outcome = _select_v61b_rewitness_outcome(
        bridge_posture=bridge_binding.selected_bridge_office_posture,
        egress_posture=egress.selected_egress_posture,
    )
    witness_basis_ref_or_none = (
        egress.communication_egress_id
        if rewitness_outcome == "witness_candidate_promoted"
        else None
    )
    field_origin_tags = {
        "rewitness_outcome": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
        "rewitness_basis_summary": "current_turn_derived",
        "root_origin_dedup_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "rewitness_outcome": [
            ingress.communication_ingress_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            continuation_refresh_decision.refresh_decision_id,
            V61B_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [],
        "rewitness_basis_summary": [
            ingress.communication_ingress_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            V61B_FROZEN_POLICY_REF,
        ],
        "root_origin_dedup_summary": [
            ingress.communication_ingress_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
        ],
    }
    reason_codes = [
        f"rewitness_outcome_{rewitness_outcome}",
        "positive_rewitness_requires_explicit_basis",
        "rewitness_non_mutating_for_v60_state",
    ]
    return AgenticDeMessageRewitnessGateRecord(
        target_arc=V61B_TARGET_ARC,
        target_path=V61B_TARGET_PATH,
        communication_ingress_ref=ingress.communication_ingress_id,
        ingress_interpretation_ref=interpretation.ingress_interpretation_id,
        communication_egress_ref=egress.communication_egress_id,
        bridge_office_binding_ref=bridge_binding.bridge_office_binding_id,
        task_charter_ref=task_charter.charter_id,
        latest_continuation_basis_ref=continuation_refresh_decision.refresh_decision_id,
        rewitness_outcome=rewitness_outcome,
        rewitness_reason_codes=reason_codes,
        frozen_policy_anchor_ref=V61B_FROZEN_POLICY_REF,
        rewitness_basis_summary=(
            "shipped V61-A communication lineage + explicit V61-B bridge binding + frozen "
            "V61-B policy anchor"
        ),
        witness_basis_ref_or_none=witness_basis_ref_or_none,
        certificate_ref_or_none=None,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=[
            *bridge_binding.root_origin_ids,
            f"rewitness:{rewitness_outcome}",
        ],
        root_origin_dedup_summary=(
            "communication ingress, interpretation, egress, and bridge-binding refs are "
            "deduplicated by shared resident seam and continuation lineage roots"
        ),
        evidence_refs=[
            ingress.communication_ingress_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            continuation_refresh_decision.refresh_decision_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_governed_communication_v61b(
    *,
    repo_root_path: Path | None = None,
    v60a_task_charter_path: Path = DEFAULT_V60A_TASK_CHARTER_PATH,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    lane_drift_path: Path = DEFAULT_V61B_LANE_DRIFT_PATH,
    v61a_evidence_path: Path = DEFAULT_V61A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> tuple[
    AgenticDeBridgeOfficeBindingRecord,
    AgenticDeMessageRewitnessGateRecord,
]:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V61-B communication")
    root = raw_root.resolve()

    path_args = {
        "v60a_task_charter_path": v60a_task_charter_path,
        "v60a_loop_state_ledger_path": v60a_loop_state_ledger_path,
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "lane_drift_path": lane_drift_path,
        "v61a_evidence_path": v61a_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v61b_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v61b_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v61a_evidence_payload(
        _load_json_object(resolved_paths["v61a_evidence_path"], error_label="V61-A evidence")
    )

    v60a_task_charter = load_task_charter_packet(resolved_paths["v60a_task_charter_path"])
    v60a_loop_state_ledger = load_loop_state_ledger(resolved_paths["v60a_loop_state_ledger_path"])
    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61a_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    v61a_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    v61a_egress = load_communication_egress_packet(resolved_paths["v61a_communication_egress_path"])

    _validate_v61b_v61a_surfaces(
        task_charter=v60a_task_charter,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        egress=v61a_egress,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_charter_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_loop_state_ledger_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61a_evidence_path"]),
    ]

    bridge_binding = _build_v61b_bridge_office_binding_record(
        task_charter=v60a_task_charter,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        egress=v61a_egress,
        evidence_refs=evidence_refs,
    )
    rewitness_gate = _build_v61b_message_rewitness_gate_record(
        task_charter=v60a_task_charter,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        interpretation=v61a_interpretation,
        egress=v61a_egress,
        bridge_binding=bridge_binding,
        evidence_refs=evidence_refs,
    )
    return bridge_binding, rewitness_gate


def _validate_v61c_v61b_surfaces(
    *,
    task_charter: AgenticDeTaskCharterPacket,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    rewitness_gate: AgenticDeMessageRewitnessGateRecord,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V61-C requires the shipped exact downstream V60 selected path")
    if ingress.target_arc != V61A_TARGET_ARC or ingress.target_path != V61A_TARGET_PATH:
        raise ValueError("V61-C requires the shipped V61-A communication ingress surface")
    if descriptor.target_arc != V61A_TARGET_ARC or descriptor.target_path != V61A_TARGET_PATH:
        raise ValueError("V61-C requires the shipped V61-A surface authority descriptor")
    if (
        interpretation.target_arc != V61A_TARGET_ARC
        or interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V61-C requires the shipped V61-A ingress interpretation surface")
    if egress.target_arc != V61A_TARGET_ARC or egress.target_path != V61A_TARGET_PATH:
        raise ValueError("V61-C requires the shipped V61-A communication egress surface")
    if ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V61-C requires the shipped exact resident V61-A API route")
    if ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V61-C requires the shipped exact resident V61-A runtime method")
    if ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V61-C requires the shipped exact resident V61-A surface class")
    if descriptor.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V61-C descriptor must bind the shipped V61-A ingress packet")
    if interpretation.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V61-C interpretation must bind the shipped V61-A ingress packet")
    if (
        interpretation.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V61-C interpretation must bind the shipped V61-A descriptor")
    if interpretation.task_charter_ref != task_charter.charter_id:
        raise ValueError("V61-C interpretation must bind the shipped V60 task charter")
    if (
        interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V61-C interpretation must bind the shipped V60-B refresh decision")
    if egress.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V61-C egress must bind the shipped V61-A interpretation")
    if egress.task_charter_ref != task_charter.charter_id:
        raise ValueError("V61-C egress must bind the shipped V60 task charter")
    if (
        egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V61-C egress must bind the shipped V60-B refresh decision")
    if egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V61-C requires the shipped exact resident V61-A egress seam")
    if (
        bridge_binding.target_arc != V61B_TARGET_ARC
        or bridge_binding.target_path != V61B_TARGET_PATH
    ):
        raise ValueError("V61-C requires the shipped V61-B bridge-office binding surface")
    if bridge_binding.frozen_policy_anchor_ref != V61B_FROZEN_POLICY_REF:
        raise ValueError("V61-C requires the shipped V61-B bridge binding policy anchor")
    if (
        rewitness_gate.target_arc != V61B_TARGET_ARC
        or rewitness_gate.target_path != V61B_TARGET_PATH
    ):
        raise ValueError("V61-C requires the shipped V61-B message rewitness gate surface")
    if rewitness_gate.frozen_policy_anchor_ref != V61B_FROZEN_POLICY_REF:
        raise ValueError("V61-C requires the shipped V61-B rewitness policy anchor")
    if bridge_binding.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V61-C bridge binding must bind the shipped V61-A ingress packet")
    if (
        bridge_binding.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V61-C bridge binding must bind the shipped V61-A descriptor")
    if bridge_binding.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V61-C bridge binding must bind the shipped V61-A interpretation")
    if bridge_binding.communication_egress_ref != egress.communication_egress_id:
        raise ValueError("V61-C bridge binding must bind the shipped V61-A egress packet")
    if bridge_binding.task_charter_ref != task_charter.charter_id:
        raise ValueError("V61-C bridge binding must bind the shipped V60 task charter")
    if (
        bridge_binding.latest_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V61-C bridge binding must bind the shipped V60-B refresh decision")
    if rewitness_gate.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V61-C rewitness gate must bind the shipped V61-A ingress packet")
    if rewitness_gate.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V61-C rewitness gate must bind the shipped V61-A interpretation")
    if rewitness_gate.communication_egress_ref != egress.communication_egress_id:
        raise ValueError("V61-C rewitness gate must bind the shipped V61-A egress packet")
    if rewitness_gate.bridge_office_binding_ref != bridge_binding.bridge_office_binding_id:
        raise ValueError("V61-C rewitness gate must bind the shipped V61-B bridge binding")
    if rewitness_gate.task_charter_ref != task_charter.charter_id:
        raise ValueError("V61-C rewitness gate must bind the shipped V60 task charter")
    if (
        rewitness_gate.latest_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V61-C rewitness gate must bind the shipped V60-B refresh decision")
    if bridge_binding.selected_bridge_office_posture != "resident_bridge_bound":
        raise ValueError("V61-C requires the shipped resident_bridge_bound V61-B posture")
    if rewitness_gate.rewitness_outcome != "witness_candidate_promoted":
        raise ValueError("V61-C requires the shipped witness_candidate_promoted V61-B posture")
    if not (rewitness_gate.witness_basis_ref_or_none or rewitness_gate.certificate_ref_or_none):
        raise ValueError(
            "V61-C requires the shipped V61-B rewitness record to carry explicit positive basis"
        )


def _build_v61c_governed_communication_hardening_register(
    *,
    task_charter: AgenticDeTaskCharterPacket,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    rewitness_gate: AgenticDeMessageRewitnessGateRecord,
    evidence_refs: list[str],
) -> AgenticDeGovernedCommunicationHardeningRegister:
    root_origin_ids = [
        f"ingress:{ingress.communication_ingress_id}",
        f"descriptor:{descriptor.surface_authority_descriptor_id}",
        f"interpretation:{interpretation.ingress_interpretation_id}",
        f"egress:{egress.communication_egress_id}",
        f"bridge:{bridge_binding.bridge_office_binding_id}",
        f"rewitness:{rewitness_gate.message_rewitness_gate_id}",
        f"charter:{task_charter.charter_id}",
        f"continuation:{continuation_refresh_decision.refresh_decision_id}",
        f"policy:{V61C_FROZEN_POLICY_REF}",
    ]
    field_origin_tags = {
        "latest_continuation_basis_selection_summary": "prior_artifact",
        "selected_bridge_office_posture": "prior_artifact",
        "rewitness_outcome": "prior_artifact",
        "positive_rewitness_witness_basis_ref_or_none": "prior_artifact",
        "positive_rewitness_certificate_ref_or_none": "prior_artifact",
        "frozen_policy_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "verdict_basis_summary": "current_turn_derived",
        "recommended_outcome": "current_turn_derived",
    }
    field_dependence_tags = {
        "latest_continuation_basis_selection_summary": [
            continuation_refresh_decision.refresh_decision_id,
            bridge_binding.bridge_office_binding_id,
        ],
        "selected_bridge_office_posture": [
            bridge_binding.bridge_office_binding_id,
        ],
        "rewitness_outcome": [
            rewitness_gate.message_rewitness_gate_id,
        ],
        "positive_rewitness_witness_basis_ref_or_none": [
            rewitness_gate.message_rewitness_gate_id,
        ],
        "positive_rewitness_certificate_ref_or_none": [
            rewitness_gate.message_rewitness_gate_id,
        ],
        "frozen_policy_ref": [],
        "evidence_basis_summary": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            rewitness_gate.message_rewitness_gate_id,
            task_charter.charter_id,
            continuation_refresh_decision.refresh_decision_id,
            V61C_FROZEN_POLICY_REF,
        ],
        "verdict_basis_summary": [
            bridge_binding.bridge_office_binding_id,
            rewitness_gate.message_rewitness_gate_id,
            continuation_refresh_decision.refresh_decision_id,
            *root_origin_ids,
        ],
        "recommended_outcome": [
            bridge_binding.bridge_office_binding_id,
            rewitness_gate.message_rewitness_gate_id,
            continuation_refresh_decision.refresh_decision_id,
            V61C_FROZEN_POLICY_REF,
        ],
    }
    entry = AgenticDeGovernedCommunicationHardeningEntry(
        communication_ingress_ref=ingress.communication_ingress_id,
        surface_authority_descriptor_ref=descriptor.surface_authority_descriptor_id,
        ingress_interpretation_ref=interpretation.ingress_interpretation_id,
        communication_egress_ref=egress.communication_egress_id,
        bridge_office_binding_ref=bridge_binding.bridge_office_binding_id,
        message_rewitness_gate_ref=rewitness_gate.message_rewitness_gate_id,
        task_charter_ref=task_charter.charter_id,
        latest_continuation_basis_ref=continuation_refresh_decision.refresh_decision_id,
        latest_continuation_basis_selection_summary=(
            bridge_binding.latest_continuation_basis_selection_summary
        ),
        selected_bridge_office_posture=bridge_binding.selected_bridge_office_posture,
        rewitness_outcome=rewitness_gate.rewitness_outcome,
        positive_rewitness_witness_basis_ref_or_none=rewitness_gate.witness_basis_ref_or_none,
        positive_rewitness_certificate_ref_or_none=rewitness_gate.certificate_ref_or_none,
        selected_hardening_target_surface=(
            "shipped_v61a_v61b_governed_communication_lineage_over_continuity_bound_"
            "create_new_exemplar_only"
        ),
        frozen_policy_ref=V61C_FROZEN_POLICY_REF,
        evidence_basis_summary=(
            "shipped V61-A communication ingress/descriptor/interpretation/egress plus "
            "shipped V61-B bridge-office binding and rewitness over the same exact "
            "continuity-bound create_new exemplar with explicit positive rewitness basis "
            "carry-through"
        ),
        verdict_basis_summary=(
            "the exact resident send seam stayed preserved, bridge-office posture remained "
            "resident_bridge_bound, rewitness remained witness_candidate_promoted with "
            "explicit positive basis carry-through, latest continuation basis selection "
            "remained explicit, and provenance/dedup remained explicit under one frozen "
            "V61-C policy anchor"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated communication-lineage artifacts remain non-independent advisory support"
        ),
        recommended_outcome="candidate_for_later_communication_hardening",
        rationale=(
            "the exact shipped V61-A/V61-B governed communication lineage now has typed "
            "communication packets, replayable bridge-office binding, explicit positive "
            "rewitness basis carry-through, and explicit continuation-basis selection, so "
            "it is a valid later path-level communication hardening candidate, but any "
            "broader communication, bridge-office, rewitness, connector, remote, repo, or "
            "execution scope still requires a later explicit lock"
        ),
        reason_codes=[
            "bridge_posture_resident_bridge_bound",
            "rewitness_outcome_witness_candidate_promoted",
            "positive_rewitness_basis_explicitly_carried",
            "latest_continuation_basis_selection_explicit",
            "path_level_only",
            "extensional_replayable_policy",
            "lineage_root_dedup_applied",
            "candidate_non_entitling_and_non_escalating",
            "later_lock_required_for_scope",
            "no_live_mutation_in_v61c",
            "non_generalizing_by_default",
        ],
        evidence_refs=evidence_refs,
    )
    return AgenticDeGovernedCommunicationHardeningRegister(
        target_arc=V61C_TARGET_ARC,
        target_path=V61C_TARGET_PATH,
        baseline_checker_version=V61C_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


def run_agentic_de_governed_communication_v61c(
    *,
    repo_root_path: Path | None = None,
    v60a_task_charter_path: Path = DEFAULT_V60A_TASK_CHARTER_PATH,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v61b_bridge_office_binding_path: Path = DEFAULT_V61B_BRIDGE_OFFICE_BINDING_PATH,
    v61b_message_rewitness_gate_path: Path = DEFAULT_V61B_MESSAGE_REWITNESS_GATE_PATH,
    lane_drift_path: Path = DEFAULT_V61C_LANE_DRIFT_PATH,
    v61a_evidence_path: Path = DEFAULT_V61A_EVIDENCE_PATH,
    v61b_evidence_path: Path = DEFAULT_V61B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeGovernedCommunicationHardeningRegister:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V61-C communication")
    root = raw_root.resolve()

    path_args = {
        "v60a_task_charter_path": v60a_task_charter_path,
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v61b_bridge_office_binding_path": v61b_bridge_office_binding_path,
        "v61b_message_rewitness_gate_path": v61b_message_rewitness_gate_path,
        "lane_drift_path": lane_drift_path,
        "v61a_evidence_path": v61a_evidence_path,
        "v61b_evidence_path": v61b_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v61c_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v61c_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v61a_evidence_payload(
        _load_json_object(resolved_paths["v61a_evidence_path"], error_label="V61-A evidence")
    )
    _validate_v61b_evidence_payload(
        _load_json_object(resolved_paths["v61b_evidence_path"], error_label="V61-B evidence")
    )

    v60a_task_charter = load_task_charter_packet(resolved_paths["v60a_task_charter_path"])
    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61a_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    v61a_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    v61a_egress = load_communication_egress_packet(resolved_paths["v61a_communication_egress_path"])
    v61b_bridge_binding = load_bridge_office_binding_record(
        resolved_paths["v61b_bridge_office_binding_path"]
    )
    v61b_rewitness_gate = load_message_rewitness_gate_record(
        resolved_paths["v61b_message_rewitness_gate_path"]
    )

    _validate_v61c_v61b_surfaces(
        task_charter=v60a_task_charter,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        egress=v61a_egress,
        bridge_binding=v61b_bridge_binding,
        rewitness_gate=v61b_rewitness_gate,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_charter_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61b_bridge_office_binding_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61b_message_rewitness_gate_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61b_evidence_path"]),
    ]
    return _build_v61c_governed_communication_hardening_register(
        task_charter=v60a_task_charter,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        egress=v61a_egress,
        bridge_binding=v61b_bridge_binding,
        rewitness_gate=v61b_rewitness_gate,
        evidence_refs=evidence_refs,
    )


def _normalize_timestamp(value: datetime | None) -> datetime | None:
    if value is None:
        return None
    if value.tzinfo is None:
        return value.replace(tzinfo=timezone.utc)
    return value


def _validate_v62a_connector_snapshot(
    *,
    snapshot: ConnectorSnapshotResponse,
    expected_session_id: str,
    min_acceptable_ts: datetime | None,
) -> None:
    if snapshot.provider != V62A_SELECTED_CONNECTOR_PROVIDER:
        raise ValueError("V62-A requires the codex provider on the selected connector path")
    if snapshot.session_id != expected_session_id:
        raise ValueError("V62-A connector snapshot must bind the shipped V60 resident session")
    if not snapshot.snapshot_id.strip():
        raise ValueError("V62-A connector snapshot requires snapshot_id")
    if not snapshot.capability_snapshot_id.strip():
        raise ValueError("V62-A connector snapshot requires capability_snapshot_id")
    if len(snapshot.connector_snapshot_hash) != 64:
        raise ValueError("V62-A connector snapshot requires a sha256 connector_snapshot_hash")
    if not snapshot.exposed_connectors:
        raise ValueError("V62-A requires at least one exposed connector on the selected path")
    exposure_ids = [item.connector_id for item in snapshot.connector_exposure if item.exposed]
    exposed_ids = _extract_v62a_connector_ids(
        items=snapshot.exposed_connectors,
        field_name="snapshot.exposed_connectors",
    )
    if exposure_ids != exposed_ids:
        raise ValueError("V62-A connector snapshot must keep exposed connectors aligned")
    normalized_created_at = _normalize_timestamp(snapshot.created_at)
    normalized_min_ts = _normalize_timestamp(min_acceptable_ts)
    if (
        normalized_created_at is not None
        and normalized_min_ts is not None
        and normalized_created_at < normalized_min_ts
    ):
        raise ValueError("V62-A connector snapshot is older than min_acceptable_ts")


def _validate_v62a_v61a_surfaces(
    *,
    task_charter: AgenticDeTaskCharterPacket,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V62-A requires the shipped exact downstream V60 selected path")
    if ingress.target_arc != V61A_TARGET_ARC or ingress.target_path != V61A_TARGET_PATH:
        raise ValueError("V62-A requires the shipped V61-A communication ingress surface")
    if descriptor.target_arc != V61A_TARGET_ARC or descriptor.target_path != V61A_TARGET_PATH:
        raise ValueError("V62-A requires the shipped V61-A surface authority descriptor")
    if (
        interpretation.target_arc != V61A_TARGET_ARC
        or interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V62-A requires the shipped V61-A ingress interpretation surface")
    if ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V62-A requires the shipped exact resident V61-A API route")
    if ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V62-A requires the shipped exact resident V61-A runtime method")
    if ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V62-A requires the shipped exact resident V61-A surface class")
    if descriptor.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V62-A descriptor must bind the shipped V61-A ingress packet")
    if interpretation.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V62-A interpretation must bind the shipped V61-A ingress packet")
    if (
        interpretation.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V62-A interpretation must bind the shipped V61-A descriptor")
    if interpretation.task_charter_ref != task_charter.charter_id:
        raise ValueError("V62-A interpretation must bind the shipped V60 task charter")
    if interpretation.loop_state_ledger_ref != loop_state_ledger.ledger_id:
        raise ValueError("V62-A interpretation must bind the shipped V60 loop-state ledger")
    if (
        interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-A interpretation must bind the shipped V60-B refresh decision")
    if ingress.resident_session_ref != loop_state_ledger.resident_session_ref:
        raise ValueError("V62-A requires the shipped V61-A resident session identity")


def _extract_v62a_connector_ids(*, items: list[dict[str, object]], field_name: str) -> list[str]:
    connector_ids: list[str] = []
    for index, item in enumerate(items):
        connector_id = item.get("id")
        if not isinstance(connector_id, str) or not connector_id.strip():
            raise ValueError(
                f"{field_name}[{index}] must carry one non-empty string id "
                "for V62-A connector admission"
            )
        connector_ids.append(connector_id)
    return connector_ids


def _build_v62a_connector_admission_record(
    *,
    loop_state_ledger: AgenticDeLoopStateLedger,
    snapshot: ConnectorSnapshotResponse,
    snapshot_ref: str,
    min_acceptable_ts: datetime | None,
    evidence_refs: list[str],
) -> AgenticDeConnectorAdmissionRecord:
    exposed_ids = _extract_v62a_connector_ids(
        items=snapshot.exposed_connectors,
        field_name="snapshot.exposed_connectors",
    )
    connector_ids = _extract_v62a_connector_ids(
        items=snapshot.connectors,
        field_name="snapshot.connectors",
    )
    exposure_ids = [item.connector_id for item in snapshot.connector_exposure]
    field_origin_tags = {
        "connector_provider_class": "prior_artifact",
        "connector_identity_facts": "prior_artifact",
        "connector_exposure_basis_ref_or_summary": "prior_artifact",
        "freshness_basis_summary": "current_turn_derived",
        "selected_connector_principal_class": "shaping_only",
        "admission_verdict": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "connector_provider_class": [snapshot_ref],
        "connector_identity_facts": [snapshot_ref],
        "connector_exposure_basis_ref_or_summary": [snapshot_ref],
        "freshness_basis_summary": [snapshot_ref],
        "selected_connector_principal_class": [V62A_FROZEN_POLICY_REF],
        "admission_verdict": [snapshot_ref, V62A_FROZEN_POLICY_REF],
        "frozen_policy_anchor_ref": [V62A_FROZEN_POLICY_REF],
    }
    min_ts_summary = (
        _normalize_timestamp(min_acceptable_ts).isoformat()
        if _normalize_timestamp(min_acceptable_ts) is not None
        else "not_provided"
    )
    return AgenticDeConnectorAdmissionRecord(
        target_arc=V62A_TARGET_ARC,
        target_path=V62A_TARGET_PATH,
        resident_session_ref=loop_state_ledger.resident_session_ref,
        connector_snapshot_ref=snapshot_ref,
        connector_snapshot_hash=snapshot.connector_snapshot_hash,
        capability_snapshot_ref=snapshot.capability_snapshot_id,
        connector_provider_class=V62A_SELECTED_CONNECTOR_PROVIDER,
        connector_identity_facts=(
            "connector snapshot exposes connector ids="
            + ",".join(connector_ids)
            + " for one codex-backed admitted connector path"
        ),
        connector_exposure_basis_ref_or_summary=(
            "snapshot exposed connector ids="
            + ",".join(exposed_ids)
            + "; connector_exposure entries="
            + ",".join(exposure_ids)
        ),
        connector_route_basis_summary=(
            "selected routes="
            f"{V62A_SELECTED_CONNECTOR_CREATE_ROUTE},"
            f"{V62A_SELECTED_CONNECTOR_GET_ROUTE}"
        ),
        freshness_basis_summary=(
            "execution_mode=live; created_at="
            + _normalize_timestamp(snapshot.created_at).isoformat()
            + "; min_acceptable_ts="
            + min_ts_summary
        ),
        selected_connector_principal_class=V62A_SELECTED_CONNECTOR_PRINCIPAL,
        frozen_policy_anchor_ref=V62A_FROZEN_POLICY_REF,
        admission_verdict="admitted",
        reason_codes=[
            "snapshot_basis_present",
            "exposure_basis_present",
            "freshness_basis_satisfied",
            "external_assistant_principal_selected_only",
            "connector_path_admitted",
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "connector snapshot basis and shaping refs remain non-independent; "
            "no connector transport authority is inferred from repeated snapshot fields"
        ),
        evidence_refs=evidence_refs,
    )


def _build_v62a_external_assistant_ingress_bridge_packet(
    *,
    connector_admission: AgenticDeConnectorAdmissionRecord,
    interpretation: AgenticDeIngressInterpretationRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    evidence_refs: list[str],
) -> AgenticDeExternalAssistantIngressBridgePacket:
    field_origin_tags = {
        "selected_connector_principal_class": "shaping_only",
        "external_assistant_payload_facts": "prior_artifact",
        "latest_continuation_basis_ref_or_equivalent": "prior_artifact",
        "frozen_policy_anchor_ref": "shaping_only",
        "bridge_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "selected_connector_principal_class": [connector_admission.connector_admission_id],
        "external_assistant_payload_facts": [
            connector_admission.connector_admission_id,
            interpretation.ingress_interpretation_id,
        ],
        "latest_continuation_basis_ref_or_equivalent": [
            interpretation.latest_v60_continuation_basis_ref
        ],
        "frozen_policy_anchor_ref": [V62A_FROZEN_POLICY_REF],
        "bridge_basis_summary": [
            connector_admission.connector_admission_id,
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            V62A_FROZEN_POLICY_REF,
        ],
    }
    return AgenticDeExternalAssistantIngressBridgePacket(
        target_arc=V62A_TARGET_ARC,
        target_path=V62A_TARGET_PATH,
        connector_admission_ref=connector_admission.connector_admission_id,
        selected_connector_principal_class=V62A_SELECTED_CONNECTOR_PRINCIPAL,
        external_assistant_payload_facts=(
            "admitted external assistant ingress over connector snapshot "
            + connector_admission.connector_snapshot_hash[:12]
            + " consumes shipped V61-A ingress/descriptor/interpretation only"
        ),
        consumed_communication_ingress_ref=ingress.communication_ingress_id,
        consumed_surface_authority_descriptor_ref=descriptor.surface_authority_descriptor_id,
        consumed_ingress_interpretation_ref=interpretation.ingress_interpretation_id,
        latest_continuation_basis_ref_or_equivalent=interpretation.latest_v60_continuation_basis_ref,
        frozen_policy_anchor_ref=V62A_FROZEN_POLICY_REF,
        bridge_basis_summary=(
            "admitted connector path plus shipped V61-A ingress/descriptor/interpretation "
            "over the exact resident send seam, without V61-B bridge-office or rewitness "
            "consumption in V62-A"
        ),
        reason_codes=[
            "admitted_connector_basis_consumed",
            "v61a_communication_basis_consumed",
            "external_assistant_principal_only",
            "ingress_only_in_v62a",
            "connector_transport_non_authorizing",
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "connector admission and shipped V61-A lineage remain non-independent bridge "
            "basis; repeated lineage refs do not mint connector authority"
        ),
        evidence_refs=evidence_refs,
    )


def run_agentic_de_connector_admission_v62a(
    *,
    repo_root_path: Path | None = None,
    v60a_task_charter_path: Path = DEFAULT_V60A_TASK_CHARTER_PATH,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    connector_snapshot_path: Path = DEFAULT_V62A_CONNECTOR_SNAPSHOT_PATH,
    lane_drift_path: Path = DEFAULT_V62A_LANE_DRIFT_PATH,
    v61a_evidence_path: Path = DEFAULT_V61A_EVIDENCE_PATH,
    v61b_evidence_path: Path = DEFAULT_V61B_EVIDENCE_PATH,
    v61c_evidence_path: Path = DEFAULT_V61C_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    min_acceptable_ts: datetime | None = None,
) -> tuple[AgenticDeConnectorAdmissionRecord, AgenticDeExternalAssistantIngressBridgePacket]:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V62-A connector admission")
    root = raw_root.resolve()

    path_args = {
        "v60a_task_charter_path": v60a_task_charter_path,
        "v60a_loop_state_ledger_path": v60a_loop_state_ledger_path,
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "connector_snapshot_path": connector_snapshot_path,
        "lane_drift_path": lane_drift_path,
        "v61a_evidence_path": v61a_evidence_path,
        "v61b_evidence_path": v61b_evidence_path,
        "v61c_evidence_path": v61c_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v62a_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v62a_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v61a_evidence_payload(
        _load_json_object(resolved_paths["v61a_evidence_path"], error_label="V61-A evidence")
    )
    _validate_v61b_evidence_payload(
        _load_json_object(resolved_paths["v61b_evidence_path"], error_label="V61-B evidence")
    )
    _validate_v61c_evidence_payload(
        _load_json_object(resolved_paths["v61c_evidence_path"], error_label="V61-C evidence")
    )

    v60a_task_charter = load_task_charter_packet(resolved_paths["v60a_task_charter_path"])
    v60a_loop_state_ledger = load_loop_state_ledger(resolved_paths["v60a_loop_state_ledger_path"])
    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61a_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    v61a_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    connector_snapshot = load_connector_snapshot_response(resolved_paths["connector_snapshot_path"])

    _validate_v62a_v61a_surfaces(
        task_charter=v60a_task_charter,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        target_relative_path=target_relative_path,
    )
    _validate_v62a_connector_snapshot(
        snapshot=connector_snapshot,
        expected_session_id=v60a_loop_state_ledger.resident_session_ref,
        min_acceptable_ts=min_acceptable_ts,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_task_charter_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_loop_state_ledger_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["connector_snapshot_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61b_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61c_evidence_path"]),
    ]
    connector_snapshot_ref = _render_input_ref(
        repo_root_path=root,
        path=resolved_paths["connector_snapshot_path"],
    )
    admission = _build_v62a_connector_admission_record(
        loop_state_ledger=v60a_loop_state_ledger,
        snapshot=connector_snapshot,
        snapshot_ref=connector_snapshot_ref,
        min_acceptable_ts=min_acceptable_ts,
        evidence_refs=evidence_refs,
    )
    bridge_packet = _build_v62a_external_assistant_ingress_bridge_packet(
        connector_admission=admission,
        interpretation=v61a_interpretation,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        evidence_refs=evidence_refs,
    )
    return admission, bridge_packet


def _validate_v62b_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    connector_admission: AgenticDeConnectorAdmissionRecord,
    ingress_bridge: AgenticDeExternalAssistantIngressBridgePacket,
    communication_egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    rewitness_gate: AgenticDeMessageRewitnessGateRecord,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V62-B requires the shipped exact downstream V60 selected path")
    if (
        connector_admission.target_arc != V62A_TARGET_ARC
        or connector_admission.target_path != V62A_TARGET_PATH
    ):
        raise ValueError("V62-B requires the shipped V62-A connector admission surface")
    if (
        ingress_bridge.target_arc != V62A_TARGET_ARC
        or ingress_bridge.target_path != V62A_TARGET_PATH
    ):
        raise ValueError("V62-B requires the shipped V62-A ingress bridge surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V62-B requires the shipped V61-A communication egress surface")
    if (
        bridge_binding.target_arc != V61B_TARGET_ARC
        or bridge_binding.target_path != V61B_TARGET_PATH
    ):
        raise ValueError("V62-B requires the shipped V61-B bridge binding surface")
    if (
        rewitness_gate.target_arc != V61B_TARGET_ARC
        or rewitness_gate.target_path != V61B_TARGET_PATH
    ):
        raise ValueError("V62-B requires the shipped V61-B rewitness gate surface")
    if connector_admission.frozen_policy_anchor_ref != V62A_FROZEN_POLICY_REF:
        raise ValueError("V62-B requires the shipped V62-A connector admission policy anchor")
    if ingress_bridge.frozen_policy_anchor_ref != V62A_FROZEN_POLICY_REF:
        raise ValueError("V62-B requires the shipped V62-A ingress bridge policy anchor")
    if bridge_binding.frozen_policy_anchor_ref != V61B_FROZEN_POLICY_REF:
        raise ValueError("V62-B requires the shipped V61-B bridge binding policy anchor")
    if rewitness_gate.frozen_policy_anchor_ref != V61B_FROZEN_POLICY_REF:
        raise ValueError("V62-B requires the shipped V61-B rewitness gate policy anchor")
    if connector_admission.connector_provider_class != V62A_SELECTED_CONNECTOR_PROVIDER:
        raise ValueError("V62-B requires the shipped V62-A codex connector provider")
    if connector_admission.admission_verdict != "admitted":
        raise ValueError("V62-B requires the shipped V62-A admitted connector verdict")
    if connector_admission.selected_connector_principal_class != V62A_SELECTED_CONNECTOR_PRINCIPAL:
        raise ValueError("V62-B requires the shipped V62-A external_assistant principal only")
    if ingress_bridge.connector_admission_ref != connector_admission.connector_admission_id:
        raise ValueError("V62-B ingress bridge must bind the shipped V62-A connector admission")
    if ingress_bridge.selected_connector_principal_class != V62A_SELECTED_CONNECTOR_PRINCIPAL:
        raise ValueError("V62-B requires the shipped V62-A ingress bridge principal selection")
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V62-B requires the shipped exact resident V61-A egress seam")
    if (
        communication_egress.ingress_interpretation_ref
        != ingress_bridge.consumed_ingress_interpretation_ref
    ):
        raise ValueError(
            "V62-B communication egress must bind the shipped V62-A interpretation basis"
        )
    if (
        ingress_bridge.latest_continuation_basis_ref_or_equivalent
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-B requires the shipped V62-A ingress bridge continuation basis")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-B requires the shipped V61-A egress continuation basis")
    if bridge_binding.communication_egress_ref != communication_egress.communication_egress_id:
        raise ValueError("V62-B bridge binding must bind the shipped V61-A egress packet")
    if (
        bridge_binding.communication_ingress_ref
        != ingress_bridge.consumed_communication_ingress_ref
    ):
        raise ValueError("V62-B bridge binding must bind the shipped V62-A ingress basis")
    if (
        bridge_binding.surface_authority_descriptor_ref
        != ingress_bridge.consumed_surface_authority_descriptor_ref
    ):
        raise ValueError("V62-B bridge binding must bind the shipped V62-A descriptor basis")
    if (
        bridge_binding.ingress_interpretation_ref
        != ingress_bridge.consumed_ingress_interpretation_ref
    ):
        raise ValueError("V62-B bridge binding must bind the shipped V62-A interpretation basis")
    if (
        bridge_binding.latest_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-B bridge binding must bind the shipped V60-B refresh decision")
    if bridge_binding.selected_bridge_office_posture != "resident_bridge_bound":
        raise ValueError("V62-B requires resident_bridge_bound on the shipped V61-B bridge binding")
    if rewitness_gate.communication_egress_ref != communication_egress.communication_egress_id:
        raise ValueError("V62-B rewitness gate must bind the shipped V61-A egress packet")
    if (
        rewitness_gate.communication_ingress_ref
        != ingress_bridge.consumed_communication_ingress_ref
    ):
        raise ValueError("V62-B rewitness gate must bind the shipped V62-A ingress basis")
    if (
        rewitness_gate.ingress_interpretation_ref
        != ingress_bridge.consumed_ingress_interpretation_ref
    ):
        raise ValueError("V62-B rewitness gate must bind the shipped V62-A interpretation basis")
    if rewitness_gate.bridge_office_binding_ref != bridge_binding.bridge_office_binding_id:
        raise ValueError("V62-B rewitness gate must bind the shipped V61-B bridge binding")
    if (
        rewitness_gate.latest_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-B rewitness gate must bind the shipped V60-B refresh decision")
    if rewitness_gate.rewitness_outcome != "witness_candidate_promoted":
        raise ValueError(
            "V62-B requires witness_candidate_promoted on the shipped V61-B rewitness gate"
        )
    if not (rewitness_gate.witness_basis_ref_or_none or rewitness_gate.certificate_ref_or_none):
        raise ValueError("V62-B requires explicit positive rewitness basis or certificate")


def _build_v62b_external_assistant_egress_bridge_packet(
    *,
    connector_admission: AgenticDeConnectorAdmissionRecord,
    ingress_bridge: AgenticDeExternalAssistantIngressBridgePacket,
    communication_egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    rewitness_gate: AgenticDeMessageRewitnessGateRecord,
    evidence_refs: list[str],
) -> AgenticDeExternalAssistantEgressBridgePacket:
    rewitness_basis_summary = (
        "positive rewitness basis carried from shipped V61-B: "
        f"witness_basis_ref_or_none={rewitness_gate.witness_basis_ref_or_none or 'none'}; "
        f"certificate_ref_or_none={rewitness_gate.certificate_ref_or_none or 'none'}"
    )
    field_origin_tags = {
        "selected_connector_principal_class": "shaping_only",
        "external_assistant_egress_payload_facts_or_summary": "current_turn_derived",
        "consumed_rewitness_basis_summary_or_none": "prior_artifact",
        "latest_continuation_basis_selection_summary": "prior_artifact",
        "frozen_policy_anchor_ref": "shaping_only",
        "bridge_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "selected_connector_principal_class": [connector_admission.connector_admission_id],
        "external_assistant_egress_payload_facts_or_summary": [
            connector_admission.connector_admission_id,
            communication_egress.communication_egress_id,
        ],
        "consumed_rewitness_basis_summary_or_none": [rewitness_gate.message_rewitness_gate_id],
        "latest_continuation_basis_selection_summary": [bridge_binding.bridge_office_binding_id],
        "frozen_policy_anchor_ref": [V62B_FROZEN_POLICY_REF],
        "bridge_basis_summary": [
            connector_admission.connector_admission_id,
            ingress_bridge.ingress_bridge_packet_id,
            communication_egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            rewitness_gate.message_rewitness_gate_id,
            V62B_FROZEN_POLICY_REF,
        ],
    }
    return AgenticDeExternalAssistantEgressBridgePacket(
        target_arc=V62B_TARGET_ARC,
        target_path=V62B_TARGET_PATH,
        connector_admission_ref=connector_admission.connector_admission_id,
        ingress_bridge_packet_ref=ingress_bridge.ingress_bridge_packet_id,
        selected_connector_principal_class=V62A_SELECTED_CONNECTOR_PRINCIPAL,
        external_assistant_egress_payload_facts_or_summary=(
            "external assistant egress over admitted connector snapshot "
            + connector_admission.connector_snapshot_hash[:12]
            + " consumes shipped V61-A egress plus explicit V61-B bridge and rewitness basis"
        ),
        consumed_communication_egress_ref=communication_egress.communication_egress_id,
        consumed_bridge_office_binding_ref_or_none=bridge_binding.bridge_office_binding_id,
        consumed_message_rewitness_gate_ref_or_none=rewitness_gate.message_rewitness_gate_id,
        consumed_rewitness_basis_summary_or_none=rewitness_basis_summary,
        latest_continuation_basis_ref_or_equivalent=(
            communication_egress.latest_v60_continuation_basis_ref
        ),
        latest_continuation_basis_selection_summary=(
            bridge_binding.latest_continuation_basis_selection_summary
        ),
        frozen_policy_anchor_ref=V62B_FROZEN_POLICY_REF,
        bridge_basis_summary=(
            "shipped V62-A connector admission + shipped V62-A ingress bridge + shipped "
            "V61-A communication egress + explicit V61-B bridge-office binding and "
            "positive rewitness basis over the same exact external_assistant connector path"
        ),
        reason_codes=[
            "admitted_connector_basis_consumed",
            "shipped_v62a_ingress_bridge_consumed",
            "shipped_v61a_communication_egress_consumed",
            "explicit_v61b_bridge_office_binding_consumed",
            "explicit_positive_rewitness_basis_carried",
            "external_assistant_principal_only",
            "egress_only_in_v62b",
            "connector_transport_non_authorizing",
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "connector admission, shipped ingress bridge, shipped V61-A egress, and shipped "
            "V61-B bridge/rewitness lineage remain non-independent; repeated consumed refs do "
            "not mint outbound connector authority"
        ),
        evidence_refs=[
            connector_admission.connector_admission_id,
            ingress_bridge.ingress_bridge_packet_id,
            communication_egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            rewitness_gate.message_rewitness_gate_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_external_assistant_egress_bridge_v62b(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v61b_bridge_office_binding_path: Path = DEFAULT_V61B_BRIDGE_OFFICE_BINDING_PATH,
    v61b_message_rewitness_gate_path: Path = DEFAULT_V61B_MESSAGE_REWITNESS_GATE_PATH,
    v62a_connector_admission_path: Path = DEFAULT_V62A_CONNECTOR_ADMISSION_PATH,
    v62a_external_assistant_ingress_bridge_path: Path = (
        DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH
    ),
    lane_drift_path: Path = DEFAULT_V62B_LANE_DRIFT_PATH,
    v62a_evidence_path: Path = DEFAULT_V62A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeExternalAssistantEgressBridgePacket:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V62-B external assistant bridge")
    root = raw_root.resolve()

    path_args = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v61b_bridge_office_binding_path": v61b_bridge_office_binding_path,
        "v61b_message_rewitness_gate_path": v61b_message_rewitness_gate_path,
        "v62a_connector_admission_path": v62a_connector_admission_path,
        "v62a_external_assistant_ingress_bridge_path": v62a_external_assistant_ingress_bridge_path,
        "lane_drift_path": lane_drift_path,
        "v62a_evidence_path": v62a_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v62b_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v62b_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v62a_evidence_payload(
        _load_json_object(resolved_paths["v62a_evidence_path"], error_label="V62-A evidence")
    )

    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    v61b_bridge_binding = load_bridge_office_binding_record(
        resolved_paths["v61b_bridge_office_binding_path"]
    )
    v61b_rewitness_gate = load_message_rewitness_gate_record(
        resolved_paths["v61b_message_rewitness_gate_path"]
    )
    v62a_connector_admission = load_connector_admission_record(
        resolved_paths["v62a_connector_admission_path"]
    )
    v62a_ingress_bridge = load_external_assistant_ingress_bridge_packet(
        resolved_paths["v62a_external_assistant_ingress_bridge_path"]
    )

    _validate_v62b_consumed_surfaces(
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        connector_admission=v62a_connector_admission,
        ingress_bridge=v62a_ingress_bridge,
        communication_egress=v61a_communication_egress,
        bridge_binding=v61b_bridge_binding,
        rewitness_gate=v61b_rewitness_gate,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61b_bridge_office_binding_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61b_message_rewitness_gate_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v62a_connector_admission_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v62a_external_assistant_ingress_bridge_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v62a_evidence_path"]),
    ]
    return _build_v62b_external_assistant_egress_bridge_packet(
        connector_admission=v62a_connector_admission,
        ingress_bridge=v62a_ingress_bridge,
        communication_egress=v61a_communication_egress,
        bridge_binding=v61b_bridge_binding,
        rewitness_gate=v61b_rewitness_gate,
        evidence_refs=evidence_refs,
    )


def _validate_v62c_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    connector_admission: AgenticDeConnectorAdmissionRecord,
    ingress_bridge: AgenticDeExternalAssistantIngressBridgePacket,
    egress_bridge: AgenticDeExternalAssistantEgressBridgePacket,
    communication_egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    rewitness_gate: AgenticDeMessageRewitnessGateRecord,
    governed_hardening: AgenticDeGovernedCommunicationHardeningRegister,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V62-C requires the shipped exact downstream V60 selected path")
    if (
        connector_admission.target_arc != V62A_TARGET_ARC
        or connector_admission.target_path != V62A_TARGET_PATH
    ):
        raise ValueError("V62-C requires the shipped V62-A connector admission surface")
    if (
        ingress_bridge.target_arc != V62A_TARGET_ARC
        or ingress_bridge.target_path != V62A_TARGET_PATH
    ):
        raise ValueError("V62-C requires the shipped V62-A ingress bridge surface")
    if egress_bridge.target_arc != V62B_TARGET_ARC or egress_bridge.target_path != V62B_TARGET_PATH:
        raise ValueError("V62-C requires the shipped V62-B egress bridge surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V62-C requires the shipped V61-A communication egress surface")
    if (
        bridge_binding.target_arc != V61B_TARGET_ARC
        or bridge_binding.target_path != V61B_TARGET_PATH
    ):
        raise ValueError("V62-C requires the shipped V61-B bridge binding surface")
    if (
        rewitness_gate.target_arc != V61B_TARGET_ARC
        or rewitness_gate.target_path != V61B_TARGET_PATH
    ):
        raise ValueError("V62-C requires the shipped V61-B rewitness gate surface")
    if (
        governed_hardening.target_arc != V61C_TARGET_ARC
        or governed_hardening.target_path != V61C_TARGET_PATH
    ):
        raise ValueError("V62-C requires the shipped V61-C governed hardening surface")
    if connector_admission.frozen_policy_anchor_ref != V62A_FROZEN_POLICY_REF:
        raise ValueError("V62-C requires the shipped V62-A connector admission policy anchor")
    if ingress_bridge.frozen_policy_anchor_ref != V62A_FROZEN_POLICY_REF:
        raise ValueError("V62-C requires the shipped V62-A ingress bridge policy anchor")
    if egress_bridge.frozen_policy_anchor_ref != V62B_FROZEN_POLICY_REF:
        raise ValueError("V62-C requires the shipped V62-B egress bridge policy anchor")
    if bridge_binding.frozen_policy_anchor_ref != V61B_FROZEN_POLICY_REF:
        raise ValueError("V62-C requires the shipped V61-B bridge binding policy anchor")
    if rewitness_gate.frozen_policy_anchor_ref != V61B_FROZEN_POLICY_REF:
        raise ValueError("V62-C requires the shipped V61-B rewitness gate policy anchor")
    if governed_hardening.entry_count != 1 or len(governed_hardening.entries) != 1:
        raise ValueError("V62-C requires the shipped V61-C single-entry advisory register")
    if governed_hardening.explicit_frozen_policy_anchor_required is not True:
        raise ValueError("V62-C requires the shipped V61-C explicit frozen-policy anchor")
    if governed_hardening.committed_lane_artifacts_outrank_narrative_docs is not True:
        raise ValueError("V62-C requires the shipped V61-C committed-artifact precedence")
    governed_entry = governed_hardening.entries[0]
    if governed_entry.frozen_policy_ref != V61C_FROZEN_POLICY_REF:
        raise ValueError("V62-C requires the shipped V61-C advisory policy anchor")
    if governed_entry.recommended_outcome != "candidate_for_later_communication_hardening":
        raise ValueError(
            "V62-C requires the shipped V61-C communication-hardening candidate posture"
        )
    if connector_admission.connector_provider_class != V62A_SELECTED_CONNECTOR_PROVIDER:
        raise ValueError("V62-C requires the shipped V62-A codex connector provider")
    if connector_admission.admission_verdict != "admitted":
        raise ValueError("V62-C requires the shipped V62-A admitted connector verdict")
    if connector_admission.selected_connector_principal_class != V62A_SELECTED_CONNECTOR_PRINCIPAL:
        raise ValueError("V62-C requires the shipped V62-A external_assistant principal only")
    if ingress_bridge.connector_admission_ref != connector_admission.connector_admission_id:
        raise ValueError("V62-C ingress bridge must bind the shipped V62-A connector admission")
    if (
        ingress_bridge.latest_continuation_basis_ref_or_equivalent
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-C requires the shipped V62-A ingress bridge continuation basis")
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V62-C requires the shipped exact resident V61-A egress seam")
    if egress_bridge.connector_admission_ref != connector_admission.connector_admission_id:
        raise ValueError("V62-C egress bridge must bind the shipped V62-A connector admission")
    if egress_bridge.ingress_bridge_packet_ref != ingress_bridge.ingress_bridge_packet_id:
        raise ValueError("V62-C egress bridge must bind the shipped V62-A ingress bridge")
    if (
        egress_bridge.consumed_communication_egress_ref
        != communication_egress.communication_egress_id
    ):
        raise ValueError("V62-C egress bridge must bind the shipped V61-A egress packet")
    if (
        egress_bridge.consumed_bridge_office_binding_ref_or_none
        != bridge_binding.bridge_office_binding_id
    ):
        raise ValueError("V62-C egress bridge must bind the shipped V61-B bridge binding")
    if (
        egress_bridge.consumed_message_rewitness_gate_ref_or_none
        != rewitness_gate.message_rewitness_gate_id
    ):
        raise ValueError("V62-C egress bridge must bind the shipped V61-B rewitness gate")
    if (
        egress_bridge.latest_continuation_basis_ref_or_equivalent
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V62-C requires the shipped V62-B continuation basis selection")
    if (
        egress_bridge.latest_continuation_basis_selection_summary
        != bridge_binding.latest_continuation_basis_selection_summary
    ):
        raise ValueError("V62-C requires the shipped V62-B continuation selection summary")
    if communication_egress.communication_egress_id != governed_entry.communication_egress_ref:
        raise ValueError("V62-C requires the shipped V61-C egress lineage")
    if bridge_binding.bridge_office_binding_id != governed_entry.bridge_office_binding_ref:
        raise ValueError("V62-C requires the shipped V61-C bridge binding lineage")
    if rewitness_gate.message_rewitness_gate_id != governed_entry.message_rewitness_gate_ref:
        raise ValueError("V62-C requires the shipped V61-C rewitness lineage")
    if (
        ingress_bridge.consumed_ingress_interpretation_ref
        != governed_entry.ingress_interpretation_ref
    ):
        raise ValueError("V62-C requires the shipped V61-C interpretation lineage")
    if (
        continuation_refresh_decision.refresh_decision_id
        != governed_entry.latest_continuation_basis_ref
    ):
        raise ValueError("V62-C requires the shipped V61-C continuation basis")
    if (
        bridge_binding.latest_continuation_basis_selection_summary
        != governed_entry.latest_continuation_basis_selection_summary
    ):
        raise ValueError("V62-C requires the shipped V61-C continuation selection summary")
    if (
        bridge_binding.selected_bridge_office_posture
        != governed_entry.selected_bridge_office_posture
    ):
        raise ValueError("V62-C requires the shipped V61-C bridge-office posture")
    if rewitness_gate.rewitness_outcome != governed_entry.rewitness_outcome:
        raise ValueError("V62-C requires the shipped V61-C rewitness posture")
    if (
        rewitness_gate.witness_basis_ref_or_none
        != governed_entry.positive_rewitness_witness_basis_ref_or_none
    ):
        raise ValueError(
            "V62-C requires the shipped V61-C positive rewitness witness-basis carry-through"
        )
    if (
        rewitness_gate.certificate_ref_or_none
        != governed_entry.positive_rewitness_certificate_ref_or_none
    ):
        raise ValueError(
            "V62-C requires the shipped V61-C positive rewitness certificate carry-through"
        )


def _build_v62c_connector_bridge_hardening_register(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    connector_admission: AgenticDeConnectorAdmissionRecord,
    ingress_bridge: AgenticDeExternalAssistantIngressBridgePacket,
    egress_bridge: AgenticDeExternalAssistantEgressBridgePacket,
    communication_egress: AgenticDeCommunicationEgressPacket,
    bridge_binding: AgenticDeBridgeOfficeBindingRecord,
    rewitness_gate: AgenticDeMessageRewitnessGateRecord,
    governed_hardening: AgenticDeGovernedCommunicationHardeningRegister,
    evidence_refs: list[str],
) -> AgenticDeConnectorBridgeHardeningRegister:
    root_origin_ids = [
        f"connector:{connector_admission.connector_admission_id}",
        f"ingress_bridge:{ingress_bridge.ingress_bridge_packet_id}",
        f"egress_bridge:{egress_bridge.egress_bridge_packet_id}",
        f"communication_egress:{communication_egress.communication_egress_id}",
        f"bridge:{bridge_binding.bridge_office_binding_id}",
        f"rewitness:{rewitness_gate.message_rewitness_gate_id}",
        f"communication_hardening:{governed_hardening.register_id}",
        f"continuation:{continuation_refresh_decision.refresh_decision_id}",
        f"policy:{V62C_FROZEN_POLICY_REF}",
    ]
    field_origin_tags = {
        "connector_provider_class": "prior_artifact",
        "selected_connector_principal_class": "prior_artifact",
        "admission_verdict": "prior_artifact",
        "latest_continuation_basis_selection_summary": "prior_artifact",
        "selected_bridge_office_posture_or_none": "prior_artifact",
        "selected_rewitness_outcome_or_none": "prior_artifact",
        "positive_rewitness_witness_basis_ref_or_none": "prior_artifact",
        "positive_rewitness_certificate_ref_or_none": "prior_artifact",
        "frozen_policy_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "verdict_basis_summary": "current_turn_derived",
        "recommended_outcome": "current_turn_derived",
    }
    field_dependence_tags = {
        "connector_provider_class": [connector_admission.connector_admission_id],
        "selected_connector_principal_class": [connector_admission.connector_admission_id],
        "admission_verdict": [connector_admission.connector_admission_id],
        "latest_continuation_basis_selection_summary": [
            egress_bridge.egress_bridge_packet_id,
            bridge_binding.bridge_office_binding_id,
            governed_hardening.register_id,
        ],
        "selected_bridge_office_posture_or_none": [
            bridge_binding.bridge_office_binding_id,
            governed_hardening.register_id,
        ],
        "selected_rewitness_outcome_or_none": [
            rewitness_gate.message_rewitness_gate_id,
            governed_hardening.register_id,
        ],
        "positive_rewitness_witness_basis_ref_or_none": [
            rewitness_gate.message_rewitness_gate_id,
            governed_hardening.register_id,
        ],
        "positive_rewitness_certificate_ref_or_none": [
            rewitness_gate.message_rewitness_gate_id,
            governed_hardening.register_id,
        ],
        "frozen_policy_ref": [],
        "evidence_basis_summary": [
            connector_admission.connector_admission_id,
            ingress_bridge.ingress_bridge_packet_id,
            egress_bridge.egress_bridge_packet_id,
            communication_egress.communication_egress_id,
            bridge_binding.bridge_office_binding_id,
            rewitness_gate.message_rewitness_gate_id,
            governed_hardening.register_id,
            continuation_refresh_decision.refresh_decision_id,
            V62C_FROZEN_POLICY_REF,
        ],
        "verdict_basis_summary": [
            connector_admission.connector_admission_id,
            egress_bridge.egress_bridge_packet_id,
            governed_hardening.register_id,
            continuation_refresh_decision.refresh_decision_id,
            *root_origin_ids,
        ],
        "recommended_outcome": [
            connector_admission.connector_admission_id,
            egress_bridge.egress_bridge_packet_id,
            governed_hardening.register_id,
            V62C_FROZEN_POLICY_REF,
        ],
    }
    entry = AgenticDeConnectorBridgeHardeningEntry(
        connector_admission_ref=connector_admission.connector_admission_id,
        ingress_bridge_packet_ref=ingress_bridge.ingress_bridge_packet_id,
        egress_bridge_packet_ref=egress_bridge.egress_bridge_packet_id,
        communication_egress_ref=communication_egress.communication_egress_id,
        bridge_office_binding_ref_or_none=bridge_binding.bridge_office_binding_id,
        message_rewitness_gate_ref_or_none=rewitness_gate.message_rewitness_gate_id,
        selected_bridge_office_posture_or_none=bridge_binding.selected_bridge_office_posture,
        selected_rewitness_outcome_or_none=rewitness_gate.rewitness_outcome,
        positive_rewitness_witness_basis_ref_or_none=rewitness_gate.witness_basis_ref_or_none,
        positive_rewitness_certificate_ref_or_none=rewitness_gate.certificate_ref_or_none,
        governed_communication_hardening_ref=governed_hardening.register_id,
        connector_provider_class=connector_admission.connector_provider_class,
        selected_connector_principal_class=connector_admission.selected_connector_principal_class,
        admission_verdict=connector_admission.admission_verdict,
        latest_continuation_basis_ref_or_equivalent=(
            continuation_refresh_decision.refresh_decision_id
        ),
        latest_continuation_basis_selection_summary=(
            bridge_binding.latest_continuation_basis_selection_summary
        ),
        selected_hardening_target_surface=(
            "shipped_v62a_v62b_external_assistant_connector_lineage_over_continuity_bound_"
            "create_new_exemplar_only"
        ),
        frozen_policy_ref=V62C_FROZEN_POLICY_REF,
        evidence_basis_summary=(
            "shipped V62-A connector admission and ingress bridge plus shipped V62-B "
            "external-assistant egress bridge, shipped V61-A communication egress, "
            "shipped V61-B bridge-office binding and rewitness, and shipped V61-C "
            "advisory hardening over the same exact continuity-bound create_new "
            "exemplar with explicit positive rewitness basis carry-through"
        ),
        verdict_basis_summary=(
            "the exact admitted codex connector path remained preserved, V62-B kept the "
            "same outbound bridge lineage, V61-B posture remained resident_bridge_bound "
            "and witness_candidate_promoted with explicit positive basis carry-through, "
            "V61-C advisory hardening remained replayable over the same lineage, and one "
            "frozen V62-C policy anchor preserved explicit provenance and non-independence "
            "dedup without minting live connector authority"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated connector admission, bridge, rewitness, and advisory lineage "
            "artifacts remain non-independent connector-hardening support"
        ),
        recommended_outcome="candidate_for_later_connector_hardening",
        rationale=(
            "the exact shipped V62-A/V62-B connector lineage now carries typed admission, "
            "replayable ingress and egress bridge basis, explicit V61-B bridge-office and "
            "positive rewitness posture, and a shipped V61-C advisory hardening register "
            "over the same lineage, so it is a valid later path-level connector hardening "
            "candidate, but any broader connector migration, fleet law, human-via-connector, "
            "remote-operator, repo, execute, or dispatch scope still requires a later "
            "explicit lock"
        ),
        reason_codes=[
            "admitted_connector_basis_consumed",
            "shipped_v62a_ingress_bridge_consumed",
            "shipped_v62b_egress_bridge_consumed",
            "shipped_v61a_communication_egress_consumed",
            "explicit_v61b_bridge_office_binding_consumed",
            "explicit_positive_rewitness_basis_carried",
            "shipped_v61c_advisory_hardening_consumed",
            "committed_artifacts_outrank_narrative_docs",
            "path_level_only",
            "extensional_replayable_policy",
            "lineage_root_dedup_applied",
            "candidate_non_entitling_and_non_escalating",
            "later_lock_required_for_scope",
            "no_live_mutation_in_v62c",
            "non_generalizing_by_default",
        ],
        evidence_refs=evidence_refs,
    )
    return AgenticDeConnectorBridgeHardeningRegister(
        target_arc=V62C_TARGET_ARC,
        target_path=V62C_TARGET_PATH,
        baseline_checker_version=V62C_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


def run_agentic_de_connector_bridge_hardening_v62c(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v61b_bridge_office_binding_path: Path = DEFAULT_V61B_BRIDGE_OFFICE_BINDING_PATH,
    v61b_message_rewitness_gate_path: Path = DEFAULT_V61B_MESSAGE_REWITNESS_GATE_PATH,
    v61c_governed_communication_hardening_path: Path = DEFAULT_V61C_HARDENING_PATH,
    v62a_connector_admission_path: Path = DEFAULT_V62A_CONNECTOR_ADMISSION_PATH,
    v62a_external_assistant_ingress_bridge_path: Path = (
        DEFAULT_V62A_EXTERNAL_ASSISTANT_INGRESS_BRIDGE_PATH
    ),
    v62b_external_assistant_egress_bridge_path: Path = (
        DEFAULT_V62B_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_PATH
    ),
    lane_drift_path: Path = DEFAULT_V62C_LANE_DRIFT_PATH,
    v62a_evidence_path: Path = DEFAULT_V62A_EVIDENCE_PATH,
    v62b_evidence_path: Path = DEFAULT_V62B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeConnectorBridgeHardeningRegister:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V62-C connector hardening")
    root = raw_root.resolve()

    path_args = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v61b_bridge_office_binding_path": v61b_bridge_office_binding_path,
        "v61b_message_rewitness_gate_path": v61b_message_rewitness_gate_path,
        "v61c_governed_communication_hardening_path": v61c_governed_communication_hardening_path,
        "v62a_connector_admission_path": v62a_connector_admission_path,
        "v62a_external_assistant_ingress_bridge_path": v62a_external_assistant_ingress_bridge_path,
        "v62b_external_assistant_egress_bridge_path": v62b_external_assistant_egress_bridge_path,
        "lane_drift_path": lane_drift_path,
        "v62a_evidence_path": v62a_evidence_path,
        "v62b_evidence_path": v62b_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v62c_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v62c_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v62a_evidence_payload(
        _load_json_object(resolved_paths["v62a_evidence_path"], error_label="V62-A evidence")
    )
    _validate_v62b_evidence_payload(
        _load_json_object(resolved_paths["v62b_evidence_path"], error_label="V62-B evidence")
    )

    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    v61b_bridge_binding = load_bridge_office_binding_record(
        resolved_paths["v61b_bridge_office_binding_path"]
    )
    v61b_rewitness_gate = load_message_rewitness_gate_record(
        resolved_paths["v61b_message_rewitness_gate_path"]
    )
    v61c_governed_hardening = load_governed_communication_hardening_register(
        resolved_paths["v61c_governed_communication_hardening_path"]
    )
    v62a_connector_admission = load_connector_admission_record(
        resolved_paths["v62a_connector_admission_path"]
    )
    v62a_ingress_bridge = load_external_assistant_ingress_bridge_packet(
        resolved_paths["v62a_external_assistant_ingress_bridge_path"]
    )
    v62b_egress_bridge = load_external_assistant_egress_bridge_packet(
        resolved_paths["v62b_external_assistant_egress_bridge_path"]
    )

    _validate_v62c_consumed_surfaces(
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        connector_admission=v62a_connector_admission,
        ingress_bridge=v62a_ingress_bridge,
        egress_bridge=v62b_egress_bridge,
        communication_egress=v61a_communication_egress,
        bridge_binding=v61b_bridge_binding,
        rewitness_gate=v61b_rewitness_gate,
        governed_hardening=v61c_governed_hardening,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61b_bridge_office_binding_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61b_message_rewitness_gate_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61c_governed_communication_hardening_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v62a_connector_admission_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v62a_external_assistant_ingress_bridge_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v62b_external_assistant_egress_bridge_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v62a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v62b_evidence_path"]),
    ]
    return _build_v62c_connector_bridge_hardening_register(
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        connector_admission=v62a_connector_admission,
        ingress_bridge=v62a_ingress_bridge,
        egress_bridge=v62b_egress_bridge,
        communication_egress=v61a_communication_egress,
        bridge_binding=v61b_bridge_binding,
        rewitness_gate=v61b_rewitness_gate,
        governed_hardening=v61c_governed_hardening,
        evidence_refs=evidence_refs,
    )


def _validate_v63a_consumed_surfaces(
    *,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if (
        loop_state_ledger.target_arc != V60A_TARGET_ARC
        or loop_state_ledger.target_path != V60A_TARGET_PATH
    ):
        raise ValueError("V63-A requires the shipped V60-A loop-state ledger surface")
    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V63-A requires the shipped V60-B continuation refresh surface")
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V63-A requires the shipped exact downstream V60 selected path")
    if ingress.target_arc != V61A_TARGET_ARC or ingress.target_path != V61A_TARGET_PATH:
        raise ValueError("V63-A requires the shipped V61-A communication ingress surface")
    if descriptor.target_arc != V61A_TARGET_ARC or descriptor.target_path != V61A_TARGET_PATH:
        raise ValueError("V63-A requires the shipped V61-A surface authority descriptor")
    if (
        interpretation.target_arc != V61A_TARGET_ARC
        or interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V63-A requires the shipped V61-A ingress interpretation surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V63-A requires the shipped V61-A communication egress surface")
    if ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V63-A requires the shipped exact resident V61-A ingress seam")
    if ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V63-A requires the shipped exact resident V61-A runtime method")
    if ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V63-A requires the shipped exact resident V61-A surface class")
    if descriptor.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V63-A descriptor must bind the shipped V61-A ingress packet")
    if interpretation.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V63-A interpretation must bind the shipped V61-A ingress packet")
    if (
        interpretation.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V63-A interpretation must bind the shipped V61-A descriptor")
    if interpretation.loop_state_ledger_ref != loop_state_ledger.ledger_id:
        raise ValueError("V63-A interpretation must bind the shipped V60-A loop-state ledger")
    if (
        interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V63-A interpretation must bind the shipped V60-B refresh decision")
    if communication_egress.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V63-A communication egress must bind the shipped V61-A interpretation")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V63-A communication egress must bind the shipped V60-B refresh decision")
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V63-A requires the shipped exact resident V61-A egress seam")
    if ingress.resident_session_ref != loop_state_ledger.resident_session_ref:
        raise ValueError("V63-A requires the shipped V61-A resident session identity")
    if descriptor.surface_instance_or_session_identity != loop_state_ledger.resident_session_ref:
        raise ValueError("V63-A descriptor must preserve the shipped resident session identity")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V63-A requires the shipped V60-B continuation policy anchor")
    if descriptor.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-A requires the shipped V61-A descriptor policy anchor")
    if interpretation.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-A requires the shipped V61-A interpretation policy anchor")
    if communication_egress.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-A requires the shipped V61-A egress policy anchor")


def _build_v63a_remote_operator_session_record(
    *,
    loop_state_ledger: AgenticDeLoopStateLedger,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    evidence_refs: list[str],
) -> AgenticDeRemoteOperatorSessionRecord:
    field_origin_tags = {
        "remote_operator_principal_class": "shaping_only",
        "remote_surface_class": "shaping_only",
        "remote_session_identity_facts": "current_turn_derived",
        "remote_surface_identity_summary": "current_turn_derived",
        "consumed_loop_state_ref": "prior_artifact",
        "consumed_communication_basis_summary": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
        "admission_verdict": "current_turn_derived",
    }
    field_dependence_tags = {
        "remote_operator_principal_class": [V63A_FROZEN_POLICY_REF],
        "remote_surface_class": [V63A_FROZEN_POLICY_REF],
        "remote_session_identity_facts": [
            loop_state_ledger.ledger_id,
            descriptor.surface_authority_descriptor_id,
        ],
        "remote_surface_identity_summary": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            communication_egress.communication_egress_id,
            V63A_FROZEN_POLICY_REF,
        ],
        "consumed_loop_state_ref": [loop_state_ledger.ledger_id],
        "consumed_communication_basis_summary": [
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            communication_egress.communication_egress_id,
        ],
        "frozen_policy_anchor_ref": [V63A_FROZEN_POLICY_REF],
        "admission_verdict": [
            loop_state_ledger.ledger_id,
            ingress.communication_ingress_id,
            descriptor.surface_authority_descriptor_id,
            interpretation.ingress_interpretation_id,
            communication_egress.communication_egress_id,
            V63A_FROZEN_POLICY_REF,
        ],
    }
    return AgenticDeRemoteOperatorSessionRecord(
        target_arc=V63A_TARGET_ARC,
        target_path=V63A_TARGET_PATH,
        remote_operator_principal_class=V63A_SELECTED_REMOTE_OPERATOR_PRINCIPAL,
        remote_surface_class=V63A_SELECTED_REMOTE_SURFACE_CLASS,
        remote_session_identity_facts=(
            "resident_session_ref="
            + loop_state_ledger.resident_session_ref
            + "; one admitted remote_operator session derived over the same exact resident "
            "session identity only"
        ),
        remote_surface_identity_summary=(
            "one read-mostly phone-safe remote operator surface over the shipped resident "
            "send/session lineage only"
        ),
        consumed_loop_state_ref=loop_state_ledger.ledger_id,
        consumed_communication_basis_summary=(
            "shipped V61-A ingress/descriptor/interpretation/egress over the exact resident "
            "send seam only"
        ),
        frozen_policy_anchor_ref=V63A_FROZEN_POLICY_REF,
        admission_verdict="admitted",
        reason_codes=[
            "remote_operator_principal_selected_only",
            "one_admitted_remote_surface_only",
            "shipped_v60_loop_state_consumed",
            "shipped_v61_communication_basis_consumed",
            "remote_transport_non_authorizing",
            "session_admitted",
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "resident session identity, shipped V60 loop-state lineage, and shipped V61 "
            "communication lineage remain non-independent remote-session basis; repeated "
            "surface facts do not mint operator authority"
        ),
        evidence_refs=evidence_refs,
    )


def _build_v63a_remote_operator_view_packet(
    *,
    session_record: AgenticDeRemoteOperatorSessionRecord,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    evidence_refs: list[str],
) -> AgenticDeRemoteOperatorViewPacket:
    consumed_communication_refs = [
        ingress.communication_ingress_id,
        descriptor.surface_authority_descriptor_id,
        interpretation.ingress_interpretation_id,
        communication_egress.communication_egress_id,
    ]
    field_origin_tags = {
        "remote_operator_session_ref": "prior_artifact",
        "consumed_loop_state_ref": "prior_artifact",
        "consumed_communication_refs": "prior_artifact",
        "task_status_summary": "current_turn_derived",
        "ask_blocker_summary": "current_turn_derived",
        "evidence_reachability_summary": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "remote_operator_session_ref": [session_record.remote_operator_session_id],
        "consumed_loop_state_ref": [loop_state_ledger.ledger_id],
        "consumed_communication_refs": consumed_communication_refs,
        "task_status_summary": [
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
        ],
        "ask_blocker_summary": [
            continuation_refresh_decision.refresh_decision_id,
            V63A_FROZEN_POLICY_REF,
        ],
        "evidence_reachability_summary": [
            continuation_refresh_decision.refresh_decision_id,
            *consumed_communication_refs,
            V63A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [V63A_FROZEN_POLICY_REF],
    }
    return AgenticDeRemoteOperatorViewPacket(
        target_arc=V63A_TARGET_ARC,
        target_path=V63A_TARGET_PATH,
        remote_operator_session_ref=session_record.remote_operator_session_id,
        consumed_loop_state_ref=loop_state_ledger.ledger_id,
        consumed_communication_refs=consumed_communication_refs,
        task_status_summary=(
            "refresh_outcome="
            + continuation_refresh_decision.refresh_outcome
            + "; selected_next_path="
            + (continuation_refresh_decision.selected_next_path_summary_or_none or "none")
            + "; selected_egress_posture="
            + communication_egress.selected_egress_posture
        ),
        ask_blocker_summary=(
            "read-mostly remote operator view may acknowledge or issue one bounded response "
            "only; richer structured answers, clarifications, inspect-rich controls, and "
            "broader command bridge semantics remain deferred to V63-B"
        ),
        evidence_reachability_summary=(
            "reachable evidence covers shipped V60-B continuation refresh plus shipped V61-A "
            "ingress/descriptor/interpretation/egress lineage under one explicit V63-A policy "
            "anchor"
        ),
        frozen_policy_anchor_ref=V63A_FROZEN_POLICY_REF,
        reason_codes=[
            "admitted_remote_session_consumed",
            "shipped_v60_refresh_basis_visible",
            "shipped_v61_communication_basis_visible",
            "read_mostly_view_only",
            "path_level_non_generalization_required",
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "remote session, shipped continuation basis, and shipped communication lineage "
            "remain non-independent view basis; repeated refs do not mint remote control "
            "authority"
        ),
        evidence_refs=evidence_refs,
    )


def _build_v63a_response_basis(
    *,
    selected_response_kind: str,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
) -> tuple[str, str, list[str]]:
    return _build_v63a_response_basis_from_resident_session_ref(
        selected_response_kind=selected_response_kind,
        resident_session_ref=loop_state_ledger.resident_session_ref,
        continuation_refresh_decision=continuation_refresh_decision,
        communication_egress=communication_egress,
    )


def _build_v63a_response_basis_from_resident_session_ref(
    *,
    selected_response_kind: str,
    resident_session_ref: str,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
) -> tuple[str, str, list[str]]:
    if selected_response_kind == "acknowledge":
        return (
            f"session:{resident_session_ref}#notification_or_session_posture",
            "acknowledge consumes shipped notification/session posture only and may not mutate "
            "continuation, communication, or authority state by itself",
            [
                "acknowledge_notification_session_only",
                "acknowledge_non_mutating",
            ],
        )
    if selected_response_kind == "approve":
        return (
            f"session:{resident_session_ref}#approval_state_or_equivalent",
            "approve consumes shipped URM approval/session posture over the selected resident "
            "session only",
            ["approve_consumes_shipped_urm_approval_session_law"],
        )
    if selected_response_kind == "continue":
        return (
            continuation_refresh_decision.refresh_decision_id,
            "continue consumes shipped V60 continuation posture over the selected refresh basis "
            "only",
            ["continue_consumes_shipped_v60_continuation_posture"],
        )
    if selected_response_kind == "pause":
        return (
            continuation_refresh_decision.refresh_decision_id,
            "pause consumes shipped V60 continuation posture over the selected refresh basis only",
            ["pause_consumes_shipped_v60_continuation_posture"],
        )
    if selected_response_kind == "escalate":
        if communication_egress.selected_egress_posture != "escalation_notice":
            raise ValueError(
                "V63-A escalate requires shipped V61-A escalation_notice egress posture"
            )
        return (
            communication_egress.communication_egress_id,
            "escalate consumes shipped V60/V61 blocked-or-escalation posture over the selected "
            "governed communication basis only",
            ["escalate_consumes_shipped_v60_v61_blocked_or_escalation_posture"],
        )
    raise ValueError(f"unsupported V63-A selected_response_kind: {selected_response_kind!r}")


def _extract_resident_session_ref_from_remote_session_identity_facts(identity_facts: str) -> str:
    prefix = "resident_session_ref="
    if not identity_facts.startswith(prefix):
        raise ValueError(
            "V63-C remote session identity facts must preserve the shipped resident session ref"
        )
    resident_session_ref, separator, _rest = identity_facts[len(prefix) :].partition(";")
    if separator != ";" or not resident_session_ref:
        raise ValueError(
            "V63-C remote session identity facts must preserve the shipped resident session ref"
        )
    return resident_session_ref


def _build_v63a_remote_operator_response_record(
    *,
    session_record: AgenticDeRemoteOperatorSessionRecord,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    selected_response_kind: str,
    evidence_refs: list[str],
) -> AgenticDeRemoteOperatorResponseRecord:
    control_basis_ref, response_basis_summary, kind_reason_codes = _build_v63a_response_basis(
        selected_response_kind=selected_response_kind,
        loop_state_ledger=loop_state_ledger,
        continuation_refresh_decision=continuation_refresh_decision,
        communication_egress=communication_egress,
    )
    field_origin_tags = {
        "remote_operator_session_ref": "prior_artifact",
        "selected_response_kind": "shaping_only",
        "consumed_control_basis_ref_or_equivalent": "current_turn_derived",
        "response_basis_summary": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "remote_operator_session_ref": [session_record.remote_operator_session_id],
        "selected_response_kind": [V63A_FROZEN_POLICY_REF],
        "consumed_control_basis_ref_or_equivalent": [
            session_record.remote_operator_session_id,
            control_basis_ref,
        ],
        "response_basis_summary": [
            session_record.remote_operator_session_id,
            control_basis_ref,
            V63A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [V63A_FROZEN_POLICY_REF],
    }
    return AgenticDeRemoteOperatorResponseRecord(
        target_arc=V63A_TARGET_ARC,
        target_path=V63A_TARGET_PATH,
        remote_operator_session_ref=session_record.remote_operator_session_id,
        selected_response_kind=selected_response_kind,
        consumed_control_basis_ref_or_equivalent=control_basis_ref,
        response_basis_summary=response_basis_summary,
        frozen_policy_anchor_ref=V63A_FROZEN_POLICY_REF,
        reason_codes=[
            "admitted_remote_session_consumed",
            "selected_response_kind_explicit",
            "control_basis_explicit",
            "typed_replayable_response_only",
            "remote_response_non_authorizing",
            *kind_reason_codes,
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "remote session and consumed control basis remain non-independent response basis; "
            "repeated control refs do not mint repo, execute, or dispatch authority"
        ),
        evidence_refs=evidence_refs,
    )


def run_agentic_de_remote_operator_starter_v63a(
    *,
    repo_root_path: Path | None = None,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    lane_drift_path: Path = DEFAULT_V63A_LANE_DRIFT_PATH,
    v61c_evidence_path: Path = DEFAULT_V61C_EVIDENCE_PATH,
    v62c_evidence_path: Path = DEFAULT_V62C_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    selected_response_kind: str = "acknowledge",
) -> tuple[
    AgenticDeRemoteOperatorSessionRecord,
    AgenticDeRemoteOperatorViewPacket,
    AgenticDeRemoteOperatorResponseRecord,
]:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V63-A remote operator starter")
    root = raw_root.resolve()

    path_args = {
        "v60a_loop_state_ledger_path": v60a_loop_state_ledger_path,
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "lane_drift_path": lane_drift_path,
        "v61c_evidence_path": v61c_evidence_path,
        "v62c_evidence_path": v62c_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v63a_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v63a_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v61c_evidence_payload(
        _load_json_object(resolved_paths["v61c_evidence_path"], error_label="V61-C evidence")
    )
    _validate_v62c_evidence_payload(
        _load_json_object(resolved_paths["v62c_evidence_path"], error_label="V62-C evidence")
    )

    v60a_loop_state_ledger = load_loop_state_ledger(resolved_paths["v60a_loop_state_ledger_path"])
    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61a_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    v61a_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    v61a_communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )

    _validate_v63a_consumed_surfaces(
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        communication_egress=v61a_communication_egress,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_loop_state_ledger_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61c_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v62c_evidence_path"]),
    ]
    session_record = _build_v63a_remote_operator_session_record(
        loop_state_ledger=v60a_loop_state_ledger,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        communication_egress=v61a_communication_egress,
        evidence_refs=evidence_refs,
    )
    view_packet = _build_v63a_remote_operator_view_packet(
        session_record=session_record,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        communication_egress=v61a_communication_egress,
        evidence_refs=evidence_refs,
    )
    response_record = _build_v63a_remote_operator_response_record(
        session_record=session_record,
        loop_state_ledger=v60a_loop_state_ledger,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        communication_egress=v61a_communication_egress,
        selected_response_kind=selected_response_kind,
        evidence_refs=evidence_refs,
    )
    return session_record, view_packet, response_record


def _validate_v63b_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    session_record: AgenticDeRemoteOperatorSessionRecord,
    view_packet: AgenticDeRemoteOperatorViewPacket,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V63-B requires the shipped V60-B continuation refresh surface")
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V63-B requires the shipped exact downstream V60 selected path")
    if ingress.target_arc != V61A_TARGET_ARC or ingress.target_path != V61A_TARGET_PATH:
        raise ValueError("V63-B requires the shipped V61-A communication ingress surface")
    if descriptor.target_arc != V61A_TARGET_ARC or descriptor.target_path != V61A_TARGET_PATH:
        raise ValueError("V63-B requires the shipped V61-A surface authority descriptor")
    if (
        interpretation.target_arc != V61A_TARGET_ARC
        or interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V63-B requires the shipped V61-A ingress interpretation surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V63-B requires the shipped V61-A communication egress surface")
    if (
        session_record.target_arc != V63A_TARGET_ARC
        or session_record.target_path != V63A_TARGET_PATH
    ):
        raise ValueError("V63-B requires the shipped V63-A remote operator session surface")
    if view_packet.target_arc != V63A_TARGET_ARC or view_packet.target_path != V63A_TARGET_PATH:
        raise ValueError("V63-B requires the shipped V63-A remote operator view surface")
    if ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V63-B requires the shipped exact resident V61-A ingress seam")
    if ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V63-B requires the shipped exact resident V61-A runtime method")
    if ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V63-B requires the shipped exact resident V61-A surface class")
    if descriptor.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V63-B descriptor must bind the shipped V61-A ingress packet")
    if interpretation.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V63-B interpretation must bind the shipped V61-A ingress packet")
    if (
        interpretation.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V63-B interpretation must bind the shipped V61-A descriptor")
    if communication_egress.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V63-B communication egress must bind the shipped V61-A interpretation")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V63-B communication egress must bind the shipped V60-B refresh decision")
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V63-B requires the shipped exact resident V61-A egress seam")
    if session_record.frozen_policy_anchor_ref != V63A_FROZEN_POLICY_REF:
        raise ValueError("V63-B requires the shipped V63-A remote session policy anchor")
    if view_packet.frozen_policy_anchor_ref != V63A_FROZEN_POLICY_REF:
        raise ValueError("V63-B requires the shipped V63-A remote view policy anchor")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V63-B requires the shipped V60-B continuation policy anchor")
    if descriptor.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-B requires the shipped V61-A descriptor policy anchor")
    if interpretation.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-B requires the shipped V61-A interpretation policy anchor")
    if communication_egress.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-B requires the shipped V61-A egress policy anchor")
    if session_record.remote_operator_principal_class != V63A_SELECTED_REMOTE_OPERATOR_PRINCIPAL:
        raise ValueError("V63-B requires the shipped V63-A remote_operator principal only")
    if session_record.remote_surface_class != V63A_SELECTED_REMOTE_SURFACE_CLASS:
        raise ValueError("V63-B requires the shipped V63-A remote surface class only")
    if session_record.admission_verdict != "admitted":
        raise ValueError("V63-B requires the shipped admitted V63-A remote session verdict")
    if view_packet.remote_operator_session_ref != session_record.remote_operator_session_id:
        raise ValueError("V63-B remote view must bind the shipped V63-A remote session")
    expected_view_refs = [
        ingress.communication_ingress_id,
        descriptor.surface_authority_descriptor_id,
        interpretation.ingress_interpretation_id,
        communication_egress.communication_egress_id,
    ]
    if view_packet.consumed_communication_refs != expected_view_refs:
        raise ValueError("V63-B remote view must preserve the shipped V61-A communication lineage")


def _build_v63b_control_basis(
    *,
    selected_intervention_kind: str,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    interpretation: AgenticDeIngressInterpretationRecord,
) -> tuple[str, str, list[str]]:
    if selected_intervention_kind == "structured_answer":
        return (
            interpretation.ingress_interpretation_id,
            "structured_answer consumes explicit shipped ask/authority-request context only and "
            "does not, by itself, mutate charter, residual, continuation, communication, "
            "bridge-office, or act-authority law",
            [
                "structured_answer_explicit_shipped_context_only",
                "richer_intervention_non_mutating",
            ],
        )
    if selected_intervention_kind == "clarification":
        return (
            ingress.communication_ingress_id,
            "clarification consumes explicit shipped communication context only and does not, by "
            "itself, mutate charter, residual, continuation, communication, bridge-office, or "
            "act-authority law",
            [
                "clarification_explicit_shipped_context_only",
                "richer_intervention_non_mutating",
            ],
        )
    if selected_intervention_kind == "inspect_rich":
        return (
            continuation_refresh_decision.refresh_decision_id,
            "inspect_rich consumes explicit shipped loop/evidence context only and does not, by "
            "itself, mutate charter, residual, continuation, communication, bridge-office, or "
            "act-authority law",
            [
                "inspect_rich_explicit_shipped_context_only",
                "richer_intervention_non_mutating",
            ],
        )
    raise ValueError(
        f"unsupported V63-B selected_intervention_kind: {selected_intervention_kind!r}"
    )


def _build_v63b_remote_operator_control_bridge_packet(
    *,
    session_record: AgenticDeRemoteOperatorSessionRecord,
    view_packet: AgenticDeRemoteOperatorViewPacket,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    interpretation: AgenticDeIngressInterpretationRecord,
    selected_intervention_kind: str,
    evidence_refs: list[str],
) -> AgenticDeRemoteOperatorControlBridgePacket:
    control_basis_ref, intervention_basis_summary, kind_reason_codes = _build_v63b_control_basis(
        selected_intervention_kind=selected_intervention_kind,
        continuation_refresh_decision=continuation_refresh_decision,
        ingress=ingress,
        interpretation=interpretation,
    )
    field_origin_tags = {
        "remote_operator_session_ref": "prior_artifact",
        "consumed_remote_view_ref_or_equivalent": "prior_artifact",
        "selected_intervention_kind": "shaping_only",
        "consumed_control_basis_ref_or_equivalent": "current_turn_derived",
        "intervention_basis_summary": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "remote_operator_session_ref": [session_record.remote_operator_session_id],
        "consumed_remote_view_ref_or_equivalent": [view_packet.remote_operator_view_id],
        "selected_intervention_kind": [V63B_FROZEN_POLICY_REF],
        "consumed_control_basis_ref_or_equivalent": [
            session_record.remote_operator_session_id,
            view_packet.remote_operator_view_id,
            control_basis_ref,
        ],
        "intervention_basis_summary": [
            session_record.remote_operator_session_id,
            view_packet.remote_operator_view_id,
            control_basis_ref,
            V63B_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [V63B_FROZEN_POLICY_REF],
    }
    return AgenticDeRemoteOperatorControlBridgePacket(
        target_arc=V63B_TARGET_ARC,
        target_path=V63B_TARGET_PATH,
        remote_operator_session_ref=session_record.remote_operator_session_id,
        consumed_remote_view_ref_or_equivalent=view_packet.remote_operator_view_id,
        selected_intervention_kind=selected_intervention_kind,
        consumed_control_basis_ref_or_equivalent=control_basis_ref,
        intervention_basis_summary=intervention_basis_summary,
        frozen_policy_anchor_ref=V63B_FROZEN_POLICY_REF,
        reason_codes=[
            "admitted_remote_session_consumed",
            "shipped_v63a_view_basis_consumed",
            "selected_intervention_kind_explicit",
            "control_basis_explicit",
            "typed_replayable_bridge_only",
            "richer_intervention_non_authorizing",
            *kind_reason_codes,
        ],
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "remote session, shipped V63-A view basis, and consumed control basis remain "
            "non-independent bridge basis; repeated refs do not mint charter, residual, "
            "continuation, communication, bridge-office, repo, execute, or dispatch authority"
        ),
        evidence_refs=evidence_refs,
    )


def run_agentic_de_remote_operator_control_bridge_v63b(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v63a_remote_operator_session_path: Path = DEFAULT_V63A_REMOTE_OPERATOR_SESSION_PATH,
    v63a_remote_operator_view_path: Path = DEFAULT_V63A_REMOTE_OPERATOR_VIEW_PATH,
    lane_drift_path: Path = DEFAULT_V63B_LANE_DRIFT_PATH,
    v63a_evidence_path: Path = DEFAULT_V63A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    selected_intervention_kind: str = "structured_answer",
) -> AgenticDeRemoteOperatorControlBridgePacket:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V63-B remote operator control bridge"
        )
    root = raw_root.resolve()

    path_args = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v63a_remote_operator_session_path": v63a_remote_operator_session_path,
        "v63a_remote_operator_view_path": v63a_remote_operator_view_path,
        "lane_drift_path": lane_drift_path,
        "v63a_evidence_path": v63a_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v63b_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v63b_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v63a_evidence_payload(
        _load_json_object(resolved_paths["v63a_evidence_path"], error_label="V63-A evidence")
    )

    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61a_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    v61a_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    v61a_communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    v63a_session_record = load_remote_operator_session_record(
        resolved_paths["v63a_remote_operator_session_path"]
    )
    v63a_view_packet = load_remote_operator_view_packet(
        resolved_paths["v63a_remote_operator_view_path"]
    )

    _validate_v63b_consumed_surfaces(
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        communication_egress=v61a_communication_egress,
        session_record=v63a_session_record,
        view_packet=v63a_view_packet,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v63a_remote_operator_session_path"],
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v63a_remote_operator_view_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v63a_evidence_path"]),
    ]
    return _build_v63b_remote_operator_control_bridge_packet(
        session_record=v63a_session_record,
        view_packet=v63a_view_packet,
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        interpretation=v61a_interpretation,
        selected_intervention_kind=selected_intervention_kind,
        evidence_refs=evidence_refs,
    )


def _validate_v63c_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    ingress: AgenticDeCommunicationIngressPacket,
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
    interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    session_record: AgenticDeRemoteOperatorSessionRecord,
    view_packet: AgenticDeRemoteOperatorViewPacket,
    response_record: AgenticDeRemoteOperatorResponseRecord | None,
    control_bridge_packet: AgenticDeRemoteOperatorControlBridgePacket | None,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V63-C requires the shipped V60-B continuation refresh surface")
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V63-C requires the shipped exact downstream V60 selected path")
    if ingress.target_arc != V61A_TARGET_ARC or ingress.target_path != V61A_TARGET_PATH:
        raise ValueError("V63-C requires the shipped V61-A communication ingress surface")
    if descriptor.target_arc != V61A_TARGET_ARC or descriptor.target_path != V61A_TARGET_PATH:
        raise ValueError("V63-C requires the shipped V61-A surface authority descriptor")
    if (
        interpretation.target_arc != V61A_TARGET_ARC
        or interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V63-C requires the shipped V61-A ingress interpretation surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V63-C requires the shipped V61-A communication egress surface")
    if ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V63-C requires the shipped exact resident V61-A ingress seam")
    if ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V63-C requires the shipped exact resident V61-A runtime method")
    if ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V63-C requires the shipped exact resident V61-A surface class")
    if descriptor.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V63-C descriptor must bind the shipped V61-A ingress packet")
    if interpretation.communication_ingress_ref != ingress.communication_ingress_id:
        raise ValueError("V63-C interpretation must bind the shipped V61-A ingress packet")
    if (
        interpretation.surface_authority_descriptor_ref
        != descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V63-C interpretation must bind the shipped V61-A descriptor")
    if communication_egress.ingress_interpretation_ref != interpretation.ingress_interpretation_id:
        raise ValueError("V63-C communication egress must bind the shipped V61-A interpretation")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V63-C communication egress must bind the shipped V60-B refresh decision")
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V63-C requires the shipped exact resident V61-A egress seam")
    if (
        session_record.target_arc != V63A_TARGET_ARC
        or session_record.target_path != V63A_TARGET_PATH
    ):
        raise ValueError("V63-C requires the shipped V63-A remote operator session surface")
    if view_packet.target_arc != V63A_TARGET_ARC or view_packet.target_path != V63A_TARGET_PATH:
        raise ValueError("V63-C requires the shipped V63-A remote operator view surface")
    if session_record.frozen_policy_anchor_ref != V63A_FROZEN_POLICY_REF:
        raise ValueError("V63-C requires the shipped V63-A remote session policy anchor")
    if view_packet.frozen_policy_anchor_ref != V63A_FROZEN_POLICY_REF:
        raise ValueError("V63-C requires the shipped V63-A remote view policy anchor")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V63-C requires the shipped V60-B continuation policy anchor")
    if descriptor.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-C requires the shipped V61-A descriptor policy anchor")
    if interpretation.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-C requires the shipped V61-A interpretation policy anchor")
    if communication_egress.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V63-C requires the shipped V61-A egress policy anchor")
    if session_record.remote_operator_principal_class != V63A_SELECTED_REMOTE_OPERATOR_PRINCIPAL:
        raise ValueError("V63-C requires the shipped V63-A remote_operator principal only")
    if session_record.remote_surface_class != V63A_SELECTED_REMOTE_SURFACE_CLASS:
        raise ValueError("V63-C requires the shipped V63-A remote surface class only")
    if session_record.admission_verdict != "admitted":
        raise ValueError("V63-C requires the shipped admitted V63-A remote session verdict")
    if view_packet.remote_operator_session_ref != session_record.remote_operator_session_id:
        raise ValueError("V63-C remote view must bind the shipped V63-A remote session")
    expected_view_refs = [
        ingress.communication_ingress_id,
        descriptor.surface_authority_descriptor_id,
        interpretation.ingress_interpretation_id,
        communication_egress.communication_egress_id,
    ]
    if view_packet.consumed_communication_refs != expected_view_refs:
        raise ValueError("V63-C remote view must preserve the shipped V61-A communication lineage")
    resident_session_ref = _extract_resident_session_ref_from_remote_session_identity_facts(
        session_record.remote_session_identity_facts
    )
    if response_record is not None:
        if (
            response_record.target_arc != V63A_TARGET_ARC
            or response_record.target_path != V63A_TARGET_PATH
        ):
            raise ValueError("V63-C requires the shipped V63-A remote response surface")
        if response_record.frozen_policy_anchor_ref != V63A_FROZEN_POLICY_REF:
            raise ValueError("V63-C requires the shipped V63-A remote response policy anchor")
        if response_record.remote_operator_session_ref != session_record.remote_operator_session_id:
            raise ValueError("V63-C remote response must bind the shipped V63-A remote session")
        expected_response_basis_ref, expected_response_basis_summary, _reason_codes = (
            _build_v63a_response_basis_from_resident_session_ref(
                selected_response_kind=response_record.selected_response_kind,
                resident_session_ref=resident_session_ref,
                continuation_refresh_decision=continuation_refresh_decision,
                communication_egress=communication_egress,
            )
        )
        if response_record.consumed_control_basis_ref_or_equivalent != expected_response_basis_ref:
            raise ValueError(
                "V63-C remote response must preserve the shipped V63-A response control basis"
            )
        if response_record.response_basis_summary != expected_response_basis_summary:
            raise ValueError(
                "V63-C remote response must preserve the shipped V63-A response basis posture"
            )
    if control_bridge_packet is not None:
        if (
            control_bridge_packet.target_arc != V63B_TARGET_ARC
            or control_bridge_packet.target_path != V63B_TARGET_PATH
        ):
            raise ValueError("V63-C requires the shipped V63-B control bridge surface")
        if control_bridge_packet.frozen_policy_anchor_ref != V63B_FROZEN_POLICY_REF:
            raise ValueError("V63-C requires the shipped V63-B control bridge policy anchor")
        if (
            control_bridge_packet.remote_operator_session_ref
            != session_record.remote_operator_session_id
        ):
            raise ValueError("V63-C control bridge must bind the shipped V63-A remote session")
        if (
            control_bridge_packet.consumed_remote_view_ref_or_equivalent
            != view_packet.remote_operator_view_id
        ):
            raise ValueError("V63-C control bridge must bind the shipped V63-A remote view")
        expected_control_basis_ref, expected_intervention_basis_summary, _reason_codes = (
            _build_v63b_control_basis(
                selected_intervention_kind=control_bridge_packet.selected_intervention_kind,
                continuation_refresh_decision=continuation_refresh_decision,
                ingress=ingress,
                interpretation=interpretation,
            )
        )
        if (
            control_bridge_packet.consumed_control_basis_ref_or_equivalent
            != expected_control_basis_ref
        ):
            raise ValueError("V63-C control bridge must preserve the shipped V63-B control basis")
        if control_bridge_packet.intervention_basis_summary != expected_intervention_basis_summary:
            raise ValueError(
                "V63-C control bridge must preserve the shipped V63-B intervention posture"
            )


def _build_v63c_remote_operator_hardening_register(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    session_record: AgenticDeRemoteOperatorSessionRecord,
    view_packet: AgenticDeRemoteOperatorViewPacket,
    response_record: AgenticDeRemoteOperatorResponseRecord | None,
    control_bridge_packet: AgenticDeRemoteOperatorControlBridgePacket | None,
    evidence_refs: list[str],
) -> AgenticDeRemoteOperatorHardeningRegister:
    root_origin_ids = [
        f"remote_session:{session_record.remote_operator_session_id}",
        f"remote_view:{view_packet.remote_operator_view_id}",
        f"communication_egress:{communication_egress.communication_egress_id}",
        f"continuation:{continuation_refresh_decision.refresh_decision_id}",
        f"policy:{V63C_FROZEN_POLICY_REF}",
    ]
    if response_record is not None:
        root_origin_ids.append(f"remote_response:{response_record.remote_operator_response_id}")
    if control_bridge_packet is not None:
        root_origin_ids.append(
            f"control_bridge:{control_bridge_packet.remote_operator_control_bridge_id}"
        )
    selected_kind_summary: str | None = None
    selected_kind_parts: list[str] = []
    if response_record is not None:
        selected_kind_parts.append(f"response_kind={response_record.selected_response_kind}")
    if control_bridge_packet is not None:
        selected_kind_parts.append(
            f"control_kind={control_bridge_packet.selected_intervention_kind}"
        )
    if selected_kind_parts:
        selected_kind_summary = "; ".join(selected_kind_parts)
    has_optional_upstream_basis = response_record is not None or control_bridge_packet is not None
    recommended_outcome = (
        "candidate_for_later_remote_operator_hardening"
        if has_optional_upstream_basis
        else "keep_warning_only"
    )
    evidence_basis_summary = (
        "shipped V63-A admitted remote session and read-mostly remote view"
        + (
            " plus shipped V63-A starter response lineage"
            if response_record is not None
            else " without shipped starter-response lineage selected"
        )
        + (
            " plus shipped V63-B richer control-bridge lineage"
            if control_bridge_packet is not None
            else " without shipped richer control-bridge lineage selected"
        )
        + (
            " over the same exact shipped V60-B continuation basis and shipped V61-A "
            "communication lineage under one explicit frozen V63-C policy anchor"
        )
    )
    verdict_basis_summary = (
        "the exact admitted remote_operator path remained preserved, shipped V63-A session/view "
        "lineage stayed authoritative, optional shipped response/control basis remained posture-"
        "consistent where selected, and one frozen V63-C policy anchor preserved explicit "
        "provenance and non-independence dedup without minting live remote, connector, repo, "
        "execute, or dispatch authority"
    )
    field_origin_tags = {
        "selected_remote_principal_class": "prior_artifact",
        "remote_session_admission_verdict": "prior_artifact",
        "selected_remote_surface_class": "prior_artifact",
        "selected_response_or_control_kind_summary_or_none": "current_turn_derived",
        "latest_continuation_basis_selection_summary": "current_turn_derived",
        "frozen_policy_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "verdict_basis_summary": "current_turn_derived",
        "recommended_outcome": "current_turn_derived",
    }
    field_dependence_tags = {
        "selected_remote_principal_class": [session_record.remote_operator_session_id],
        "remote_session_admission_verdict": [session_record.remote_operator_session_id],
        "selected_remote_surface_class": [session_record.remote_operator_session_id],
        "selected_response_or_control_kind_summary_or_none": [
            ref
            for ref in [
                (
                    response_record.remote_operator_response_id
                    if response_record is not None
                    else None
                ),
                (
                    control_bridge_packet.remote_operator_control_bridge_id
                    if control_bridge_packet is not None
                    else None
                ),
            ]
            if ref is not None
        ],
        "latest_continuation_basis_selection_summary": [
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
        ],
        "frozen_policy_ref": [],
        "evidence_basis_summary": [
            session_record.remote_operator_session_id,
            view_packet.remote_operator_view_id,
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
            *root_origin_ids,
        ],
        "verdict_basis_summary": [
            session_record.remote_operator_session_id,
            view_packet.remote_operator_view_id,
            continuation_refresh_decision.refresh_decision_id,
            *root_origin_ids,
        ],
        "recommended_outcome": [
            session_record.remote_operator_session_id,
            continuation_refresh_decision.refresh_decision_id,
            V63C_FROZEN_POLICY_REF,
        ],
    }
    entry = AgenticDeRemoteOperatorHardeningEntry(
        remote_operator_session_ref=session_record.remote_operator_session_id,
        remote_operator_view_ref=view_packet.remote_operator_view_id,
        remote_operator_response_ref_or_none=(
            response_record.remote_operator_response_id if response_record is not None else None
        ),
        remote_operator_control_bridge_ref_or_none=(
            control_bridge_packet.remote_operator_control_bridge_id
            if control_bridge_packet is not None
            else None
        ),
        selected_response_or_control_kind_summary_or_none=selected_kind_summary,
        selected_remote_principal_class=session_record.remote_operator_principal_class,
        remote_session_admission_verdict=session_record.admission_verdict,
        selected_remote_surface_class=session_record.remote_surface_class,
        latest_continuation_basis_ref_or_equivalent=continuation_refresh_decision.refresh_decision_id,
        latest_continuation_basis_selection_summary=(
            "latest shipped V60-B refresh decision remains the selected continuation basis for "
            "the exact shipped remote operator lineage only"
        ),
        selected_hardening_target_surface=(
            "shipped_v63a_v63b_remote_operator_lineage_over_one_admitted_remote_operator_path_only"
        ),
        frozen_policy_ref=V63C_FROZEN_POLICY_REF,
        evidence_basis_summary=evidence_basis_summary,
        verdict_basis_summary=verdict_basis_summary,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated remote session, view, response, control, continuation, and policy "
            "lineage artifacts remain non-independent remote-hardening support"
        ),
        recommended_outcome=recommended_outcome,
        rationale=(
            "the exact shipped V63-A/V63-B remote lineage now carries admitted session, "
            "replayable read-mostly view, optional shipped response/control exemplar basis, "
            "and one frozen V63-C advisory policy anchor, so it is a valid later path-level "
            "remote hardening candidate without minting connector, broad remote-admin, repo, "
            "execute, or dispatch authority"
            if has_optional_upstream_basis
            else "without optional shipped response/control exemplar basis, V63-C keeps the "
            "current advisory posture only and may not overread richer intervention evidence"
        ),
        reason_codes=(
            [
                "admitted_remote_session_consumed",
                "shipped_v63a_view_consumed",
                "optional_upstream_basis_posture_consistent",
                "selected_kind_summary_explicit",
                "committed_artifacts_outrank_narrative_docs",
                "path_level_only",
                "extensional_replayable_policy",
                "lineage_root_dedup_applied",
                "candidate_non_entitling_and_non_escalating",
                "later_lock_required_for_scope",
                "no_live_mutation_in_v63c",
                "non_generalizing_by_default",
            ]
            if has_optional_upstream_basis
            else [
                "admitted_remote_session_consumed",
                "shipped_v63a_view_consumed",
                "optional_upstream_basis_absent_no_overread",
                "committed_artifacts_outrank_narrative_docs",
                "path_level_only",
                "extensional_replayable_policy",
                "lineage_root_dedup_applied",
                "keep_warning_only_retains_current_advisory_posture_only",
                "no_live_mutation_in_v63c",
                "non_generalizing_by_default",
            ]
        ),
        evidence_refs=evidence_refs,
    )
    return AgenticDeRemoteOperatorHardeningRegister(
        target_arc=V63C_TARGET_ARC,
        target_path=V63C_TARGET_PATH,
        optional_upstream_basis_consistency_fails_closed=True,
        baseline_checker_version=V63C_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


def run_agentic_de_remote_operator_hardening_v63c(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v63a_remote_operator_session_path: Path = DEFAULT_V63A_REMOTE_OPERATOR_SESSION_PATH,
    v63a_remote_operator_view_path: Path = DEFAULT_V63A_REMOTE_OPERATOR_VIEW_PATH,
    v63a_remote_operator_response_path: Path | None = DEFAULT_V63A_REMOTE_OPERATOR_RESPONSE_PATH,
    v63b_remote_operator_control_bridge_path: Path
    | None = DEFAULT_V63B_REMOTE_OPERATOR_CONTROL_BRIDGE_PATH,
    lane_drift_path: Path = DEFAULT_V63C_LANE_DRIFT_PATH,
    v63a_evidence_path: Path = DEFAULT_V63A_EVIDENCE_PATH,
    v63b_evidence_path: Path = DEFAULT_V63B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeRemoteOperatorHardeningRegister:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V63-C remote hardening")
    root = raw_root.resolve()

    path_args: dict[str, Path | None] = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v63a_remote_operator_session_path": v63a_remote_operator_session_path,
        "v63a_remote_operator_view_path": v63a_remote_operator_view_path,
        "v63a_remote_operator_response_path": v63a_remote_operator_response_path,
        "v63b_remote_operator_control_bridge_path": v63b_remote_operator_control_bridge_path,
        "lane_drift_path": lane_drift_path,
        "v63a_evidence_path": v63a_evidence_path,
        "v63b_evidence_path": v63b_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        if path is None:
            continue
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v63c_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v63c_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v63a_evidence_payload(
        _load_json_object(resolved_paths["v63a_evidence_path"], error_label="V63-A evidence")
    )
    _validate_v63b_evidence_payload(
        _load_json_object(resolved_paths["v63b_evidence_path"], error_label="V63-B evidence")
    )

    v60b_continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    v61a_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61a_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    v61a_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    v61a_communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    v63a_session_record = load_remote_operator_session_record(
        resolved_paths["v63a_remote_operator_session_path"]
    )
    v63a_view_packet = load_remote_operator_view_packet(
        resolved_paths["v63a_remote_operator_view_path"]
    )
    v63a_response_record = (
        load_remote_operator_response_record(resolved_paths["v63a_remote_operator_response_path"])
        if "v63a_remote_operator_response_path" in resolved_paths
        else None
    )
    v63b_control_bridge_packet = (
        load_remote_operator_control_bridge_packet(
            resolved_paths["v63b_remote_operator_control_bridge_path"]
        )
        if "v63b_remote_operator_control_bridge_path" in resolved_paths
        else None
    )

    _validate_v63c_consumed_surfaces(
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        ingress=v61a_ingress,
        descriptor=v61a_descriptor,
        interpretation=v61a_interpretation,
        communication_egress=v61a_communication_egress,
        session_record=v63a_session_record,
        view_packet=v63a_view_packet,
        response_record=v63a_response_record,
        control_bridge_packet=v63b_control_bridge_packet,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v63a_remote_operator_session_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v63a_remote_operator_view_path"],
        ),
    ]
    if "v63a_remote_operator_response_path" in resolved_paths:
        evidence_refs.append(
            _render_input_ref(
                repo_root_path=root,
                path=resolved_paths["v63a_remote_operator_response_path"],
            )
        )
    if "v63b_remote_operator_control_bridge_path" in resolved_paths:
        evidence_refs.append(
            _render_input_ref(
                repo_root_path=root,
                path=resolved_paths["v63b_remote_operator_control_bridge_path"],
            )
        )
    evidence_refs.extend(
        [
            _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
            _render_input_ref(repo_root_path=root, path=resolved_paths["v63a_evidence_path"]),
            _render_input_ref(repo_root_path=root, path=resolved_paths["v63b_evidence_path"]),
        ]
    )
    return _build_v63c_remote_operator_hardening_register(
        continuation_refresh_decision=v60b_continuation_refresh_decision,
        communication_egress=v61a_communication_egress,
        session_record=v63a_session_record,
        view_packet=v63a_view_packet,
        response_record=v63a_response_record,
        control_bridge_packet=v63b_control_bridge_packet,
        evidence_refs=evidence_refs,
    )


def _normalize_v64a_target_relative_path(target_relative_path: str) -> Path:
    normalized_text = target_relative_path.strip()
    if not normalized_text:
        raise ValueError("target_relative_path must be non-empty for V64-A")
    relative_path = Path(normalized_text)
    if relative_path.is_absolute():
        raise ValueError("target_relative_path must remain relative for V64-A")
    if not relative_path.parts or any(part in {"", ".", ".."} for part in relative_path.parts):
        raise ValueError(
            "target_relative_path may not use empty, dot, or parent traversal parts for V64-A"
        )
    return relative_path


def _derive_v64a_surface_selection(
    *,
    target_relative_path: str,
) -> tuple[str, Path, str, str, str | None]:
    relative_target = _normalize_v64a_target_relative_path(target_relative_path)
    if relative_target.parent == Path("."):
        return (
            "declared_file_set",
            relative_target,
            (
                "declared file-set member "
                f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{relative_target.as_posix()}"
            ),
            (
                "include only the exact selected file-set member "
                f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{relative_target.as_posix()}"
            ),
            "exclude every other path under the declared continuity root by default",
        )
    surface_relative = relative_target.parent
    return (
        V64A_SELECTED_DESCRIPTOR_SURFACE_CLASS,
        surface_relative,
        (
            "declared subtree "
            f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{surface_relative.as_posix()}/"
        ),
        (
            "include only canonical normalized descendants under "
            f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{surface_relative.as_posix()}/"
        ),
        "exclude every path outside the declared subtree by default",
    )


def _assert_v64a_surface_and_target_canonical_membership(
    *,
    repo_root_path: Path,
    target_relative_path: str,
) -> tuple[Path, Path, Path, str]:
    relative_target = _normalize_v64a_target_relative_path(target_relative_path)
    surface_class, surface_relative, _identity_summary, _inclusion_summary, _exclusion_summary = (
        _derive_v64a_surface_selection(target_relative_path=target_relative_path)
    )
    continuity_root = repo_root_path / DESIGNATED_WORKSPACE_CONTINUITY_ROOT
    surface_path = continuity_root / surface_relative
    target_path = continuity_root / relative_target
    _assert_v64a_repo_local_input_path(
        repo_root_path=repo_root_path,
        candidate=continuity_root,
        field_name="declared_continuity_root",
    )
    _assert_v64a_repo_local_input_path(
        repo_root_path=repo_root_path,
        candidate=surface_path,
        field_name="selected_surface_path",
    )
    _assert_v64a_repo_local_input_path(
        repo_root_path=repo_root_path,
        candidate=target_path,
        field_name="selected_target_path",
    )
    if surface_class == "declared_subtree":
        try:
            target_path.relative_to(surface_path)
        except ValueError as exc:
            raise ValueError(
                "V64-A target path must remain inside the declared writable subtree"
            ) from exc
    elif target_path != surface_path:
        raise ValueError("V64-A file-set selection must preserve the exact selected target path")
    return relative_target, surface_path, target_path, surface_class


def _validate_v64a_consumed_surfaces(
    *,
    continuity_region: AgenticDeWorkspaceContinuityRegionDeclaration,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy_report: AgenticDeWorkspaceOccupancyReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_ingress: AgenticDeCommunicationIngressPacket,
    surface_authority_descriptor: AgenticDeSurfaceAuthorityDescriptor,
    ingress_interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if (
        continuity_region.target_arc != V59A_TARGET_ARC
        or continuity_region.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V59-A continuity region surface")
    if (
        continuity_admission.target_arc != V59A_TARGET_ARC
        or continuity_admission.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V59-A continuity admission surface")
    if (
        occupancy_report.target_arc != V59A_TARGET_ARC
        or occupancy_report.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V59-A occupancy surface")
    if (
        continuity_reintegration.target_arc != V59A_TARGET_ARC
        or continuity_reintegration.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V59-A continuity reintegration surface")
    if (
        loop_state_ledger.target_arc != V60A_TARGET_ARC
        or loop_state_ledger.target_path != V60A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V60-A loop-state ledger surface")
    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V60-B continuation refresh surface")
    if (
        communication_ingress.target_arc != V61A_TARGET_ARC
        or communication_ingress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V61-A communication ingress surface")
    if (
        surface_authority_descriptor.target_arc != V61A_TARGET_ARC
        or surface_authority_descriptor.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V61-A surface authority descriptor")
    if (
        ingress_interpretation.target_arc != V61A_TARGET_ARC
        or ingress_interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V61-A ingress interpretation surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-A requires the shipped V61-A communication egress surface")
    if (
        continuity_region.declared_continuity_root
        != DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()
    ):
        raise ValueError("V64-A requires the shipped V59 declared continuity root")
    if continuity_region.target_identity_or_target_set != target_relative_path:
        raise ValueError("V64-A requires the shipped exact V59 selected target path")
    if (
        continuity_admission.continuity_region_declaration_ref
        != continuity_region.continuity_region_id
    ):
        raise ValueError("V64-A continuity admission must bind the shipped V59 region")
    if continuity_admission.continuity_verdict != "admitted":
        raise ValueError(
            "V64-A requires admitted V59 continuity lineage before writable surface selection"
        )
    if occupancy_report.continuity_admission_ref != continuity_admission.continuity_admission_id:
        raise ValueError("V64-A occupancy must bind the shipped V59 continuity admission")
    if occupancy_report.target_relative_path != target_relative_path:
        raise ValueError("V64-A occupancy must preserve the shipped selected target path")
    if occupancy_report.occupancy_verdict != "unoccupied":
        raise ValueError("V64-A requires per-target unoccupied admissibility for create_new")
    if (
        continuity_reintegration.continuity_admission_ref
        != continuity_admission.continuity_admission_id
    ):
        raise ValueError(
            "V64-A continuity reintegration must bind the shipped continuity admission"
        )
    if continuity_reintegration.occupancy_report_ref != occupancy_report.occupancy_report_id:
        raise ValueError("V64-A continuity reintegration must bind the shipped occupancy report")
    if continuity_reintegration.continuity_reintegration_status != "reintegrated":
        raise ValueError("V64-A requires the shipped reintegrated V59 continuity lineage")
    if continuity_reintegration.continuity_witness_certificate_ref_or_equivalent is None:
        raise ValueError("V64-A requires witness-bearing V59 continuity reintegration")
    if loop_state_ledger.continuity_region_ref != continuity_region.continuity_region_id:
        raise ValueError("V64-A loop-state ledger must bind the shipped continuity region")
    if (
        loop_state_ledger.latest_continuity_reintegration_ref_or_none
        != continuity_reintegration.report_id
    ):
        raise ValueError(
            "V64-A loop-state ledger must preserve the shipped continuity reintegration basis"
        )
    if continuation_refresh_decision.prior_loop_state_ledger_ref != loop_state_ledger.ledger_id:
        raise ValueError("V64-A continuation refresh must bind the shipped V60-A loop-state ledger")
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V64-A requires the shipped exact V60 selected downstream path")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V64-A requires the shipped V60-B continuation policy anchor")
    if communication_ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V64-A requires the shipped exact resident V61-A ingress seam")
    if communication_ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V64-A requires the shipped exact resident V61-A runtime method")
    if communication_ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V64-A requires the shipped exact resident V61-A surface class")
    if (
        surface_authority_descriptor.communication_ingress_ref
        != communication_ingress.communication_ingress_id
    ):
        raise ValueError("V64-A surface descriptor must bind the shipped V61-A ingress packet")
    if (
        ingress_interpretation.communication_ingress_ref
        != communication_ingress.communication_ingress_id
    ):
        raise ValueError("V64-A ingress interpretation must bind the shipped V61-A ingress packet")
    if (
        ingress_interpretation.surface_authority_descriptor_ref
        != surface_authority_descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V64-A ingress interpretation must bind the shipped V61-A descriptor")
    if ingress_interpretation.loop_state_ledger_ref != loop_state_ledger.ledger_id:
        raise ValueError(
            "V64-A ingress interpretation must preserve the shipped V60-A loop-state ledger"
        )
    if (
        ingress_interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError(
            "V64-A ingress interpretation must preserve the shipped V60-B continuation basis"
        )
    if (
        communication_egress.ingress_interpretation_ref
        != ingress_interpretation.ingress_interpretation_id
    ):
        raise ValueError("V64-A communication egress must bind the shipped V61-A interpretation")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError(
            "V64-A communication egress must preserve the shipped V60-B continuation basis"
        )
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V64-A requires the shipped exact resident V61-A egress seam")
    if surface_authority_descriptor.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V64-A requires the shipped V61-A descriptor policy anchor")
    if ingress_interpretation.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V64-A requires the shipped V61-A interpretation policy anchor")
    if communication_egress.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V64-A requires the shipped V61-A egress policy anchor")


def _build_v64a_repo_writable_surface_descriptor(
    *,
    continuity_region: AgenticDeWorkspaceContinuityRegionDeclaration,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy_report: AgenticDeWorkspaceOccupancyReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeRepoWritableSurfaceDescriptor:
    (
        surface_class,
        _surface_relative,
        selected_surface_identity_summary,
        explicit_inclusion_basis_summary,
        explicit_exclusion_basis_summary_or_none,
    ) = _derive_v64a_surface_selection(target_relative_path=target_relative_path)
    field_origin_tags = {
        "selected_surface_identity_summary": "current_turn_derived",
        "selected_surface_class": "shaping_only",
        "canonical_membership_basis_summary": "current_turn_derived",
        "explicit_inclusion_basis_summary": "current_turn_derived",
        "explicit_exclusion_basis_summary_or_none": "current_turn_derived",
        "consumed_continuity_refs": "prior_artifact",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "selected_surface_identity_summary": [
            continuity_region.continuity_region_id,
            occupancy_report.occupancy_report_id,
        ],
        "selected_surface_class": [V64A_FROZEN_POLICY_REF],
        "canonical_membership_basis_summary": [
            continuity_region.continuity_region_id,
            continuity_admission.continuity_admission_id,
            occupancy_report.occupancy_report_id,
            continuity_reintegration.report_id,
        ],
        "explicit_inclusion_basis_summary": [continuity_region.continuity_region_id],
        "explicit_exclusion_basis_summary_or_none": [continuity_region.continuity_region_id],
        "consumed_continuity_refs": [
            continuity_region.continuity_region_id,
            continuity_admission.continuity_admission_id,
            occupancy_report.occupancy_report_id,
            continuity_reintegration.report_id,
        ],
        "frozen_policy_anchor_ref": [V64A_FROZEN_POLICY_REF],
    }
    return AgenticDeRepoWritableSurfaceDescriptor(
        target_arc=V64A_TARGET_ARC,
        target_path=V64A_TARGET_PATH,
        selected_surface_identity_summary=selected_surface_identity_summary,
        selected_surface_class=surface_class,
        canonical_membership_basis_summary=(
            "canonical normalized target and selected surface remain lexically repo-contained, "
            "symlink-free from the repository root, and resolved within the declared continuity "
            "root before writable entitlement is admitted"
        ),
        explicit_inclusion_basis_summary=explicit_inclusion_basis_summary,
        explicit_exclusion_basis_summary_or_none=explicit_exclusion_basis_summary_or_none,
        consumed_continuity_refs=[
            continuity_region.continuity_region_id,
            continuity_admission.continuity_admission_id,
            occupancy_report.occupancy_report_id,
            continuity_reintegration.report_id,
        ],
        frozen_policy_anchor_ref=V64A_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "shipped V59 continuity region, admission, occupancy, and reintegration lineage "
            "remain non-independent context for one selected writable surface only; repeated "
            "continuity evidence does not mint all-repo, shell, execute, dispatch, worker, or "
            "remote authority"
        ),
        evidence_refs=evidence_refs,
    )


def _build_v64a_repo_write_lease_record(
    *,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    continuity_region: AgenticDeWorkspaceContinuityRegionDeclaration,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy_report: AgenticDeWorkspaceOccupancyReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    loop_state_ledger: AgenticDeLoopStateLedger,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_ingress: AgenticDeCommunicationIngressPacket,
    surface_authority_descriptor: AgenticDeSurfaceAuthorityDescriptor,
    ingress_interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    evidence_refs: list[str],
) -> AgenticDeRepoWriteLeaseRecord:
    field_origin_tags = {
        "writable_surface_descriptor_ref": "prior_artifact",
        "consumed_continuity_basis_summary": "current_turn_derived",
        "consumed_continuation_basis_summary": "current_turn_derived",
        "consumed_communication_basis_summary_or_none": "current_turn_derived",
        "preserved_write_semantics_summary": "shaping_only",
        "lease_verdict": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "writable_surface_descriptor_ref": [descriptor.repo_writable_surface_descriptor_id],
        "consumed_continuity_basis_summary": [
            continuity_region.continuity_region_id,
            continuity_admission.continuity_admission_id,
            occupancy_report.occupancy_report_id,
            continuity_reintegration.report_id,
        ],
        "consumed_continuation_basis_summary": [
            loop_state_ledger.ledger_id,
            continuation_refresh_decision.refresh_decision_id,
        ],
        "consumed_communication_basis_summary_or_none": [
            communication_ingress.communication_ingress_id,
            surface_authority_descriptor.surface_authority_descriptor_id,
            ingress_interpretation.ingress_interpretation_id,
            communication_egress.communication_egress_id,
        ],
        "preserved_write_semantics_summary": [V64A_FROZEN_POLICY_REF],
        "lease_verdict": [
            descriptor.repo_writable_surface_descriptor_id,
            continuation_refresh_decision.refresh_decision_id,
            V64A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [V64A_FROZEN_POLICY_REF],
    }
    return AgenticDeRepoWriteLeaseRecord(
        target_arc=V64A_TARGET_ARC,
        target_path=V64A_TARGET_PATH,
        writable_surface_descriptor_ref=descriptor.repo_writable_surface_descriptor_id,
        consumed_continuity_basis_summary=(
            "shipped V59 continuity region, admitted continuity posture, exact target occupancy, "
            "and reintegrated continuity witness remain context and admissibility basis only; "
            "continuity state is not writable entitlement by itself"
        ),
        consumed_continuation_basis_summary=(
            "shipped V60-A loop identity plus shipped V60-B selected downstream "
            "local_write/create_new posture remain required continuation basis for the bounded "
            "repo-surface lease"
        ),
        consumed_communication_basis_summary_or_none=(
            "shipped V61-A ingress, descriptor, interpretation, and egress lineage may "
            "contextualize write posture and provenance only; governed communication is not the "
            "lease or writable authority by itself"
        ),
        preserved_write_semantics_summary=(
            "preserve local_write/create_new only; do not widen append, overwrite, rename, or "
            "delete semantics in V64-A"
        ),
        lease_verdict="admitted",
        frozen_policy_anchor_ref=V64A_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "selected writable-surface descriptor plus shipped V59/V60/V61 lineage remain "
            "non-independent lease basis; repeated continuity, continuation, or communication "
            "refs do not become ambient repo authority"
        ),
        reason_codes=[
            "selected_writable_surface_explicit",
            "continuity_context_not_entitlement",
            "continuation_basis_required",
            "communication_context_not_entitlement",
            "surface_widening_only",
            "preserved_local_write_create_new_only",
            "typed_replayable_write_lease_only",
            "no_all_repo_or_execute_dispatch_worker_authority",
        ],
        evidence_refs=evidence_refs,
    )


def _build_v64a_repo_write_surface_admission_record(
    *,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    occupancy_report: AgenticDeWorkspaceOccupancyReport,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeRepoWriteSurfaceAdmissionRecord:
    field_origin_tags = {
        "writable_surface_descriptor_ref": "prior_artifact",
        "repo_write_lease_ref": "prior_artifact",
        "selected_target_path_summary": "current_turn_derived",
        "target_membership_basis_summary": "current_turn_derived",
        "target_occupancy_or_admissibility_basis_summary": "current_turn_derived",
        "preserved_write_semantics_summary": "shaping_only",
        "admission_verdict": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "writable_surface_descriptor_ref": [descriptor.repo_writable_surface_descriptor_id],
        "repo_write_lease_ref": [lease.repo_write_lease_id],
        "selected_target_path_summary": [descriptor.repo_writable_surface_descriptor_id],
        "target_membership_basis_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            lease.repo_write_lease_id,
        ],
        "target_occupancy_or_admissibility_basis_summary": [
            occupancy_report.occupancy_report_id,
            lease.repo_write_lease_id,
        ],
        "preserved_write_semantics_summary": [V64A_FROZEN_POLICY_REF],
        "admission_verdict": [
            descriptor.repo_writable_surface_descriptor_id,
            lease.repo_write_lease_id,
            occupancy_report.occupancy_report_id,
        ],
        "frozen_policy_anchor_ref": [V64A_FROZEN_POLICY_REF],
    }
    return AgenticDeRepoWriteSurfaceAdmissionRecord(
        target_arc=V64A_TARGET_ARC,
        target_path=V64A_TARGET_PATH,
        writable_surface_descriptor_ref=descriptor.repo_writable_surface_descriptor_id,
        repo_write_lease_ref=lease.repo_write_lease_id,
        selected_target_path_summary=(
            f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
        ),
        target_membership_basis_summary=(
            "the selected target remains canonically normalized and inside the one declared "
            "writable surface; surface widening does not remove exact target-membership checks"
        ),
        target_occupancy_or_admissibility_basis_summary=(
            "shipped V59 occupancy remains unoccupied for the selected target, so one create_new "
            "admission is lawful under the bounded lease; the lease alone is not blanket "
            "entitlement for every path in the selected surface"
        ),
        preserved_write_semantics_summary=(
            "preserve local_write/create_new only; broader write-mutation semantics remain "
            "deferred beyond V64-A"
        ),
        admission_verdict="admitted",
        frozen_policy_anchor_ref=V64A_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "selected target membership, shipped occupancy, and bounded lease remain "
            "non-independent admission basis for one exact in-surface create_new path only"
        ),
        reason_codes=[
            "target_membership_explicit",
            "target_occupancy_required",
            "lease_not_blanket_entitlement",
            "preserved_local_write_create_new_only",
            "typed_replayable_target_admission_only",
            "no_shell_execute_dispatch_worker_or_all_repo_authority",
        ],
        evidence_refs=evidence_refs,
    )


def run_agentic_de_repo_writable_surface_v64a(
    *,
    repo_root_path: Path | None = None,
    v59a_continuity_region_declaration_path: Path = DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    v59a_continuity_admission_path: Path = DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    v59a_occupancy_report_path: Path = DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    v59a_continuity_reintegration_path: Path = DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    v60a_loop_state_ledger_path: Path = DEFAULT_V60A_LOOP_STATE_LEDGER_PATH,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    lane_drift_path: Path = DEFAULT_V64A_LANE_DRIFT_PATH,
    v59c_evidence_path: Path = DEFAULT_V59C_EVIDENCE_PATH,
    v60c_evidence_path: Path = DEFAULT_V60C_EVIDENCE_PATH,
    v61c_evidence_path: Path = DEFAULT_V61C_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> tuple[
    AgenticDeRepoWritableSurfaceDescriptor,
    AgenticDeRepoWriteLeaseRecord,
    AgenticDeRepoWriteSurfaceAdmissionRecord,
]:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V64-A writable surface")
    root = raw_root.resolve()
    path_args = {
        "v59a_continuity_region_declaration_path": v59a_continuity_region_declaration_path,
        "v59a_continuity_admission_path": v59a_continuity_admission_path,
        "v59a_occupancy_report_path": v59a_occupancy_report_path,
        "v59a_continuity_reintegration_path": v59a_continuity_reintegration_path,
        "v60a_loop_state_ledger_path": v60a_loop_state_ledger_path,
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "lane_drift_path": lane_drift_path,
        "v59c_evidence_path": v59c_evidence_path,
        "v60c_evidence_path": v60c_evidence_path,
        "v61c_evidence_path": v61c_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v64a_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate
    _validate_v64a_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v59c_evidence_payload(
        _load_json_object(resolved_paths["v59c_evidence_path"], error_label="V59-C evidence")
    )
    _validate_v60c_evidence_payload(
        _load_json_object(resolved_paths["v60c_evidence_path"], error_label="V60-C evidence")
    )
    _validate_v61c_evidence_payload(
        _load_json_object(resolved_paths["v61c_evidence_path"], error_label="V61-C evidence")
    )
    normalized_target_relative_path, _surface_path, _target_path, _surface_class = (
        _assert_v64a_surface_and_target_canonical_membership(
            repo_root_path=root,
            target_relative_path=target_relative_path,
        )
    )
    canonical_target_relative_path = normalized_target_relative_path.as_posix()
    continuity_region = load_workspace_continuity_region_declaration(
        resolved_paths["v59a_continuity_region_declaration_path"]
    )
    continuity_admission = load_workspace_continuity_admission_record(
        resolved_paths["v59a_continuity_admission_path"]
    )
    occupancy_report = load_workspace_occupancy_report(resolved_paths["v59a_occupancy_report_path"])
    continuity_reintegration = load_workspace_continuity_reintegration_report(
        resolved_paths["v59a_continuity_reintegration_path"]
    )
    loop_state_ledger = load_loop_state_ledger(resolved_paths["v60a_loop_state_ledger_path"])
    continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    communication_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    v61_surface_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    ingress_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    _validate_v64a_consumed_surfaces(
        continuity_region=continuity_region,
        continuity_admission=continuity_admission,
        occupancy_report=occupancy_report,
        continuity_reintegration=continuity_reintegration,
        loop_state_ledger=loop_state_ledger,
        continuation_refresh_decision=continuation_refresh_decision,
        communication_ingress=communication_ingress,
        surface_authority_descriptor=v61_surface_descriptor,
        ingress_interpretation=ingress_interpretation,
        communication_egress=communication_egress,
        target_relative_path=canonical_target_relative_path,
    )
    evidence_refs = [
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_continuity_region_declaration_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_continuity_admission_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_occupancy_report_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v59a_continuity_reintegration_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60a_loop_state_ledger_path"]),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v60b_continuation_refresh_decision_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v61a_communication_ingress_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v61a_surface_authority_descriptor_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v61a_ingress_interpretation_path"]
        ),
        _render_input_ref(
            repo_root_path=root, path=resolved_paths["v61a_communication_egress_path"]
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59c_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v60c_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v61c_evidence_path"]),
    ]
    descriptor = _build_v64a_repo_writable_surface_descriptor(
        continuity_region=continuity_region,
        continuity_admission=continuity_admission,
        occupancy_report=occupancy_report,
        continuity_reintegration=continuity_reintegration,
        target_relative_path=canonical_target_relative_path,
        evidence_refs=evidence_refs,
    )
    lease = _build_v64a_repo_write_lease_record(
        descriptor=descriptor,
        continuity_region=continuity_region,
        continuity_admission=continuity_admission,
        occupancy_report=occupancy_report,
        continuity_reintegration=continuity_reintegration,
        loop_state_ledger=loop_state_ledger,
        continuation_refresh_decision=continuation_refresh_decision,
        communication_ingress=communication_ingress,
        surface_authority_descriptor=v61_surface_descriptor,
        ingress_interpretation=ingress_interpretation,
        communication_egress=communication_egress,
        evidence_refs=evidence_refs,
    )
    admission = _build_v64a_repo_write_surface_admission_record(
        descriptor=descriptor,
        lease=lease,
        occupancy_report=occupancy_report,
        target_relative_path=canonical_target_relative_path,
        evidence_refs=evidence_refs,
    )
    return descriptor, lease, admission


def _extract_v64b_observed_write_entry(
    *,
    observation: AgenticDeLocalEffectObservationRecord,
) -> tuple[str, str]:
    if len(observation.observed_write_set) != 1:
        raise ValueError("V64-B requires one exact shipped V59-A observed write effect")
    observed_entry = observation.observed_write_set[0]
    if observed_entry.write_kind != "create_new":
        raise ValueError("V64-B requires the shipped create_new observed write kind")
    if observed_entry.existed_before is not False:
        raise ValueError("V64-B requires the shipped create_new observed write posture")
    return observed_entry.relative_path, observed_entry.content_sha256


def _validate_v64b_consumed_surfaces(
    *,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    admission: AgenticDeRepoWriteSurfaceAdmissionRecord,
    target_relative_path: str,
) -> None:
    expected_surface_class, _surface_relative, expected_surface_identity_summary, _, _ = (
        _derive_v64a_surface_selection(target_relative_path=target_relative_path)
    )
    expected_target_summary = (
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
    )
    observed_target_path, _observed_target_sha256 = _extract_v64b_observed_write_entry(
        observation=observation
    )
    if (
        descriptor.target_arc != V64A_TARGET_ARC
        or descriptor.target_path != V64A_TARGET_PATH
    ):
        raise ValueError("V64-B requires the shipped V64-A writable-surface descriptor")
    if lease.target_arc != V64A_TARGET_ARC or lease.target_path != V64A_TARGET_PATH:
        raise ValueError("V64-B requires the shipped V64-A repo write lease")
    if admission.target_arc != V64A_TARGET_ARC or admission.target_path != V64A_TARGET_PATH:
        raise ValueError("V64-B requires the shipped V64-A repo write surface admission")
    if (
        observation.target_arc != V59A_TARGET_ARC
        or observation.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V64-B requires the shipped V59-A local-effect observation surface")
    if (
        conformance.target_arc != V59A_TARGET_ARC
        or conformance.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V64-B requires the shipped V59-A local-effect conformance surface")
    if descriptor.frozen_policy_anchor_ref != V64A_FROZEN_POLICY_REF:
        raise ValueError("V64-B requires the shipped V64-A descriptor policy anchor")
    if lease.frozen_policy_anchor_ref != V64A_FROZEN_POLICY_REF:
        raise ValueError("V64-B requires the shipped V64-A lease policy anchor")
    if admission.frozen_policy_anchor_ref != V64A_FROZEN_POLICY_REF:
        raise ValueError("V64-B requires the shipped V64-A admission policy anchor")
    if descriptor.selected_surface_class != expected_surface_class:
        raise ValueError("V64-B requires the shipped V64-A selected surface class")
    if descriptor.selected_surface_identity_summary != expected_surface_identity_summary:
        raise ValueError("V64-B requires the shipped V64-A selected writable surface only")
    if lease.writable_surface_descriptor_ref != descriptor.repo_writable_surface_descriptor_id:
        raise ValueError("V64-B lease must bind the shipped V64-A writable-surface descriptor")
    if admission.writable_surface_descriptor_ref != descriptor.repo_writable_surface_descriptor_id:
        raise ValueError("V64-B admission must bind the shipped V64-A writable-surface descriptor")
    if admission.repo_write_lease_ref != lease.repo_write_lease_id:
        raise ValueError("V64-B admission must bind the shipped V64-A repo write lease")
    if lease.lease_verdict != "admitted":
        raise ValueError("V64-B requires the shipped admitted V64-A repo write lease")
    if admission.admission_verdict != "admitted":
        raise ValueError("V64-B requires the shipped admitted V64-A target admission")
    if admission.selected_target_path_summary != expected_target_summary:
        raise ValueError("V64-B requires the shipped exact V64-A admitted target path")
    if observed_target_path != expected_target_summary:
        raise ValueError("V64-B requires the shipped exact V59-A observed write-effect target")
    if observation.selected_live_action_class != "local_write":
        raise ValueError("V64-B requires the shipped V59-A local_write action class")
    if observation.selected_local_write_kind != "create_new":
        raise ValueError("V64-B requires the shipped V59-A create_new write kind")
    if observation.observation_outcome != "bounded_effect_observed":
        raise ValueError("V64-B requires the shipped bounded V59-A observed write effect")
    if observation.boundedness_verdict != "bounded":
        raise ValueError("V64-B requires bounded V59-A observation lineage")
    if conformance.observation_ref != observation.observation_id:
        raise ValueError("V64-B conformance must bind the shipped V59-A observation")
    if conformance.conformance_status != "effect_aligned":
        raise ValueError("V64-B requires shipped effect-aligned V59-A conformance")
    if conformance.boundedness_verdict != "bounded":
        raise ValueError("V64-B requires bounded V59-A conformance lineage")
    if conformance.live_effect_present is not True:
        raise ValueError("V64-B requires shipped positive V59-A write-effect lineage")


def _build_v64b_repo_write_restoration_record(
    *,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    admission: AgenticDeRepoWriteSurfaceAdmissionRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    restoration_effect: ObservedWorkspaceContinuityRestorationEffect,
    evidence_refs: list[str],
) -> AgenticDeRepoWriteRestorationRecord:
    restoration_status = (
        "restored"
        if restoration_effect.restoration_outcome == "restoration_effect_observed"
        else "rejected_target_not_restorable"
    )
    field_origin_tags = {
        "writable_surface_descriptor_ref": "prior_artifact",
        "repo_write_lease_ref": "prior_artifact",
        "repo_write_surface_admission_ref": "prior_artifact",
        "consumed_write_effect_basis_ref_or_equivalent": "prior_artifact",
        "selected_target_path_summary": "prior_artifact",
        "target_membership_basis_summary": "current_turn_derived",
        "target_occupancy_or_admissibility_basis_summary": "current_turn_derived",
        "restoration_basis_summary": "current_turn_derived",
        "preserved_write_semantics_summary": "shaping_only",
        "restoration_status": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "writable_surface_descriptor_ref": [descriptor.repo_writable_surface_descriptor_id],
        "repo_write_lease_ref": [lease.repo_write_lease_id],
        "repo_write_surface_admission_ref": [admission.repo_write_surface_admission_id],
        "consumed_write_effect_basis_ref_or_equivalent": [conformance.report_id],
        "selected_target_path_summary": [admission.repo_write_surface_admission_id],
        "target_membership_basis_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            admission.repo_write_surface_admission_id,
        ],
        "target_occupancy_or_admissibility_basis_summary": [
            admission.repo_write_surface_admission_id,
            observation.observation_id,
        ],
        "restoration_basis_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            lease.repo_write_lease_id,
            admission.repo_write_surface_admission_id,
            observation.observation_id,
            conformance.report_id,
            V64B_FROZEN_POLICY_REF,
        ],
        "preserved_write_semantics_summary": [V64B_FROZEN_POLICY_REF],
        "restoration_status": [
            admission.repo_write_surface_admission_id,
            conformance.report_id,
            restoration_effect.restoration_pre_state_ref,
            restoration_effect.restoration_post_state_ref,
        ],
        "frozen_policy_anchor_ref": [V64B_FROZEN_POLICY_REF],
    }
    return AgenticDeRepoWriteRestorationRecord(
        target_arc=V64B_TARGET_ARC,
        target_path=V64B_TARGET_PATH,
        writable_surface_descriptor_ref=descriptor.repo_writable_surface_descriptor_id,
        repo_write_lease_ref=lease.repo_write_lease_id,
        repo_write_surface_admission_ref=admission.repo_write_surface_admission_id,
        consumed_write_effect_basis_ref_or_equivalent=conformance.report_id,
        selected_target_path_summary=admission.selected_target_path_summary,
        target_membership_basis_summary=(
            "restoration reuses the shipped V64-A exact target-membership law; the same "
            "canonically normalized admitted target remains the only restorable target"
        ),
        target_occupancy_or_admissibility_basis_summary=(
            "restoration reuses the shipped V64-A occupancy/admissibility carry-through and "
            "the shipped V59-A observed create_new effect lineage; restoration does not become "
            "fresh target admission by itself"
        ),
        restoration_basis_summary=(
            "shipped V64-A writable-surface descriptor, admitted repo write lease, and exact "
            "target admission plus shipped V59-A observed and effect-aligned create_new write "
            "lineage; restoration replays one bounded compensating remove over the same exact "
            "admitted target only"
        ),
        preserved_write_semantics_summary=(
            "preserve V64-A local_write/create_new entitlement semantics only; V64-B adds one "
            "typed compensating restore over the shipped create_new effect and does not widen "
            "append, overwrite, rename, or delete authority"
        ),
        restoration_status=restoration_status,
        frozen_policy_anchor_ref=V64B_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "shipped V64-A descriptor, lease, and admission plus shipped V59-A write-effect "
            "observation and conformance remain non-independent restoration basis for one "
            "exact target only; repeated refs do not mint fresh surface, lease, target, "
            "all-repo, execute, dispatch, worker, connector, or remote-operator authority"
        ),
        reason_codes=[
            "shipped_v64a_writable_surface_basis_consumed",
            "shipped_v59a_write_effect_lineage_consumed",
            "same_selected_surface_only",
            "same_exact_admitted_target_only",
            "restoration_not_fresh_surface_or_lease_or_target_admission",
            "preserved_local_write_create_new_only",
            "typed_replayable_restoration_only",
            "no_all_repo_execute_dispatch_worker_or_remote_connector_authority",
        ],
        evidence_refs=[
            descriptor.repo_writable_surface_descriptor_id,
            lease.repo_write_lease_id,
            admission.repo_write_surface_admission_id,
            observation.observation_id,
            conformance.report_id,
            restoration_effect.restoration_pre_state_ref,
            restoration_effect.restoration_post_state_ref,
            *evidence_refs,
        ],
    )


def _build_v64b_repo_write_reintegration_report(
    *,
    restoration: AgenticDeRepoWriteRestorationRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    evidence_refs: list[str],
) -> AgenticDeRepoWriteReintegrationReport:
    reintegration_status = (
        "reintegrated"
        if restoration.restoration_status == "restored"
        else "rejected_inconsistent_basis"
    )
    field_origin_tags = {
        "repo_write_restoration_ref": "prior_artifact",
        "reintegration_basis_summary": "current_turn_derived",
        "reintegration_status": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "repo_write_restoration_ref": [restoration.repo_write_restoration_id],
        "reintegration_basis_summary": [
            restoration.repo_write_restoration_id,
            observation.observation_id,
            conformance.report_id,
            V64B_FROZEN_POLICY_REF,
        ],
        "reintegration_status": [
            restoration.repo_write_restoration_id,
            conformance.report_id,
        ],
        "frozen_policy_anchor_ref": [V64B_FROZEN_POLICY_REF],
    }
    return AgenticDeRepoWriteReintegrationReport(
        target_arc=V64B_TARGET_ARC,
        target_path=V64B_TARGET_PATH,
        repo_write_restoration_ref=restoration.repo_write_restoration_id,
        reintegration_basis_summary=(
            "the shipped exact create_new write-effect lineage remained explicit and the V64-B "
            "restoration record replayed one bounded compensating restore over the same exact "
            "admitted target under one frozen V64-B policy anchor"
        ),
        reintegration_status=reintegration_status,
        frozen_policy_anchor_ref=V64B_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "restoration record plus shipped V59-A write-effect lineage remain non-independent "
            "repo-write reintegration basis; reintegration does not widen writable authority"
        ),
        reason_codes=[
            "typed_replayable_reintegration_only",
            "same_exact_target_restoration_lineage_consumed",
            "no_fresh_surface_or_lease_or_target_admission",
            "no_all_repo_execute_dispatch_worker_or_remote_connector_authority",
        ],
        evidence_refs=[
            restoration.repo_write_restoration_id,
            observation.observation_id,
            conformance.report_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_repo_write_restoration_v64b(
    *,
    repo_root_path: Path | None = None,
    v59a_observation_path: Path = DEFAULT_V59A_OBSERVATION_PATH,
    v59a_local_effect_conformance_path: Path = DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v64a_repo_writable_surface_descriptor_path: Path = (
        DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH
    ),
    v64a_repo_write_lease_path: Path = DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    v64a_repo_write_surface_admission_path: Path = DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    lane_drift_path: Path = DEFAULT_V64B_LANE_DRIFT_PATH,
    v64a_evidence_path: Path = DEFAULT_V64A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> tuple[
    AgenticDeRepoWriteRestorationRecord,
    AgenticDeRepoWriteReintegrationReport,
]:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if raw_root.exists() and raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V64-B repo restoration")
    root = raw_root.resolve()
    path_args = {
        "v59a_observation_path": v59a_observation_path,
        "v59a_local_effect_conformance_path": v59a_local_effect_conformance_path,
        "v64a_repo_writable_surface_descriptor_path": v64a_repo_writable_surface_descriptor_path,
        "v64a_repo_write_lease_path": v64a_repo_write_lease_path,
        "v64a_repo_write_surface_admission_path": v64a_repo_write_surface_admission_path,
        "lane_drift_path": lane_drift_path,
        "v64a_evidence_path": v64a_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v64b_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate
    _validate_v64b_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v64a_evidence_payload(
        _load_json_object(resolved_paths["v64a_evidence_path"], error_label="V64-A evidence")
    )
    normalized_target_relative_path, _surface_path, _target_path, _surface_class = (
        _assert_v64a_surface_and_target_canonical_membership(
            repo_root_path=root,
            target_relative_path=target_relative_path,
        )
    )
    canonical_target_relative_path = normalized_target_relative_path.as_posix()
    observation = load_local_effect_observation_record(resolved_paths["v59a_observation_path"])
    conformance = load_local_effect_conformance_report(
        resolved_paths["v59a_local_effect_conformance_path"]
    )
    descriptor = load_repo_writable_surface_descriptor(
        resolved_paths["v64a_repo_writable_surface_descriptor_path"]
    )
    lease = load_repo_write_lease_record(resolved_paths["v64a_repo_write_lease_path"])
    admission = load_repo_write_surface_admission_record(
        resolved_paths["v64a_repo_write_surface_admission_path"]
    )
    _validate_v64b_consumed_surfaces(
        observation=observation,
        conformance=conformance,
        descriptor=descriptor,
        lease=lease,
        admission=admission,
        target_relative_path=canonical_target_relative_path,
    )
    _observed_target_path, observed_target_sha256 = _extract_v64b_observed_write_entry(
        observation=observation
    )
    restoration_effect = observe_workspace_continuity_create_new_restoration_effect(
        repo_root_path=root,
        target_relative_path=canonical_target_relative_path,
        expected_prior_governed_lineage_ref=observation.observation_id,
        expected_target_content_sha256=observed_target_sha256,
        expected_relative_paths=(admission.selected_target_path_summary,),
    )
    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=resolved_paths["v59a_observation_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v59a_local_effect_conformance_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64a_repo_writable_surface_descriptor_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v64a_repo_write_lease_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64a_repo_write_surface_admission_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v64a_evidence_path"]),
    ]
    restoration = _build_v64b_repo_write_restoration_record(
        descriptor=descriptor,
        lease=lease,
        admission=admission,
        observation=observation,
        conformance=conformance,
        restoration_effect=restoration_effect,
        evidence_refs=evidence_refs,
    )
    reintegration = _build_v64b_repo_write_reintegration_report(
        restoration=restoration,
        observation=observation,
        conformance=conformance,
        evidence_refs=evidence_refs,
    )
    return restoration, reintegration


def _validate_v64c_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_ingress: AgenticDeCommunicationIngressPacket,
    surface_authority_descriptor: AgenticDeSurfaceAuthorityDescriptor,
    ingress_interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    admission: AgenticDeRepoWriteSurfaceAdmissionRecord,
    restoration: AgenticDeRepoWriteRestorationRecord | None,
    reintegration: AgenticDeRepoWriteReintegrationReport | None,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    expected_target_summary = (
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
    )
    (
        expected_surface_class,
        _surface_relative,
        expected_surface_identity_summary,
        _inclusion_summary,
        _exclusion_summary,
    ) = _derive_v64a_surface_selection(target_relative_path=target_relative_path)

    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V64-C requires the shipped V60-B continuation refresh surface")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V60-B continuation policy anchor")
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V64-C requires the shipped exact V60 selected downstream path")
    if (
        communication_ingress.target_arc != V61A_TARGET_ARC
        or communication_ingress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-C requires the shipped V61-A communication ingress surface")
    if (
        surface_authority_descriptor.target_arc != V61A_TARGET_ARC
        or surface_authority_descriptor.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-C requires the shipped V61-A surface authority descriptor")
    if (
        ingress_interpretation.target_arc != V61A_TARGET_ARC
        or ingress_interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-C requires the shipped V61-A ingress interpretation surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V64-C requires the shipped V61-A communication egress surface")
    if communication_ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V64-C requires the shipped exact resident V61-A ingress seam")
    if communication_ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V64-C requires the shipped exact resident V61-A runtime method")
    if communication_ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V64-C requires the shipped exact resident V61-A surface class")
    if (
        surface_authority_descriptor.communication_ingress_ref
        != communication_ingress.communication_ingress_id
    ):
        raise ValueError("V64-C surface descriptor must bind the shipped V61-A ingress packet")
    if (
        ingress_interpretation.communication_ingress_ref
        != communication_ingress.communication_ingress_id
    ):
        raise ValueError("V64-C ingress interpretation must bind the shipped V61-A ingress packet")
    if (
        ingress_interpretation.surface_authority_descriptor_ref
        != surface_authority_descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V64-C ingress interpretation must bind the shipped V61-A descriptor")
    if (
        ingress_interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError(
            "V64-C ingress interpretation must preserve the shipped V60-B continuation basis"
        )
    if (
        communication_egress.ingress_interpretation_ref
        != ingress_interpretation.ingress_interpretation_id
    ):
        raise ValueError("V64-C communication egress must bind the shipped V61-A interpretation")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError(
            "V64-C communication egress must preserve the shipped V60-B continuation basis"
        )
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V64-C requires the shipped exact resident V61-A egress seam")
    if surface_authority_descriptor.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V61-A descriptor policy anchor")
    if ingress_interpretation.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V61-A interpretation policy anchor")
    if communication_egress.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V61-A egress policy anchor")

    if descriptor.target_arc != V64A_TARGET_ARC or descriptor.target_path != V64A_TARGET_PATH:
        raise ValueError("V64-C requires the shipped V64-A writable-surface descriptor")
    if lease.target_arc != V64A_TARGET_ARC or lease.target_path != V64A_TARGET_PATH:
        raise ValueError("V64-C requires the shipped V64-A repo write lease")
    if admission.target_arc != V64A_TARGET_ARC or admission.target_path != V64A_TARGET_PATH:
        raise ValueError("V64-C requires the shipped V64-A repo write surface admission")
    if descriptor.frozen_policy_anchor_ref != V64A_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V64-A descriptor policy anchor")
    if lease.frozen_policy_anchor_ref != V64A_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V64-A lease policy anchor")
    if admission.frozen_policy_anchor_ref != V64A_FROZEN_POLICY_REF:
        raise ValueError("V64-C requires the shipped V64-A admission policy anchor")
    if descriptor.selected_surface_class != expected_surface_class:
        raise ValueError("V64-C requires the shipped V64-A selected surface class")
    if descriptor.selected_surface_identity_summary != expected_surface_identity_summary:
        raise ValueError("V64-C requires the shipped V64-A selected writable surface only")
    if lease.writable_surface_descriptor_ref != descriptor.repo_writable_surface_descriptor_id:
        raise ValueError("V64-C lease must bind the shipped V64-A writable-surface descriptor")
    if admission.writable_surface_descriptor_ref != descriptor.repo_writable_surface_descriptor_id:
        raise ValueError("V64-C admission must bind the shipped V64-A writable-surface descriptor")
    if admission.repo_write_lease_ref != lease.repo_write_lease_id:
        raise ValueError("V64-C admission must bind the shipped V64-A repo write lease")
    if lease.lease_verdict != "admitted":
        raise ValueError("V64-C requires the shipped admitted V64-A repo write lease")
    if admission.admission_verdict != "admitted":
        raise ValueError("V64-C requires the shipped admitted V64-A target admission")
    if admission.selected_target_path_summary != expected_target_summary:
        raise ValueError("V64-C requires the shipped exact V64-A admitted target path")
    if reintegration is not None and restoration is None:
        raise ValueError("V64-C reintegration basis requires the shipped V64-B restoration record")

    if restoration is not None:
        if restoration.target_arc != V64B_TARGET_ARC or restoration.target_path != V64B_TARGET_PATH:
            raise ValueError("V64-C requires the shipped V64-B repo write restoration surface")
        if restoration.frozen_policy_anchor_ref != V64B_FROZEN_POLICY_REF:
            raise ValueError("V64-C requires the shipped V64-B restoration policy anchor")
        if (
            restoration.writable_surface_descriptor_ref
            != descriptor.repo_writable_surface_descriptor_id
        ):
            raise ValueError("V64-C restoration must bind the shipped V64-A descriptor")
        if restoration.repo_write_lease_ref != lease.repo_write_lease_id:
            raise ValueError("V64-C restoration must bind the shipped V64-A repo write lease")
        if (
            restoration.repo_write_surface_admission_ref
            != admission.repo_write_surface_admission_id
        ):
            raise ValueError("V64-C restoration must bind the shipped V64-A target admission")
        if restoration.selected_target_path_summary != admission.selected_target_path_summary:
            raise ValueError("V64-C restoration must preserve the shipped exact admitted target")
        if (
            restoration.preserved_write_semantics_summary
            != "preserve V64-A local_write/create_new entitlement semantics only; V64-B adds one "
            "typed compensating restore over the shipped create_new effect and does not widen "
            "append, overwrite, rename, or delete authority"
        ):
            raise ValueError(
                "V64-C restoration must preserve the shipped V64-B write-semantics posture"
            )
        if restoration.restoration_status not in {
            "restored",
            "rejected_target_not_restorable",
            "rejected_missing_basis",
            "rejected_inconsistent_basis",
        }:
            raise ValueError("V64-C restoration must preserve the shipped V64-B status family")

    if reintegration is not None:
        if (
            reintegration.target_arc != V64B_TARGET_ARC
            or reintegration.target_path != V64B_TARGET_PATH
        ):
            raise ValueError("V64-C requires the shipped V64-B repo write reintegration surface")
        if reintegration.frozen_policy_anchor_ref != V64B_FROZEN_POLICY_REF:
            raise ValueError("V64-C requires the shipped V64-B reintegration policy anchor")
        if reintegration.repo_write_restoration_ref != restoration.repo_write_restoration_id:
            raise ValueError(
                "V64-C reintegration must bind the same shipped V64-B restoration chain"
            )
        if reintegration.reintegration_status not in {
            "reintegrated",
            "rejected_missing_basis",
            "rejected_inconsistent_basis",
        }:
            raise ValueError("V64-C reintegration must preserve the shipped V64-B status family")


def _build_v64c_repo_writable_surface_hardening_register(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    admission: AgenticDeRepoWriteSurfaceAdmissionRecord,
    restoration: AgenticDeRepoWriteRestorationRecord | None,
    reintegration: AgenticDeRepoWriteReintegrationReport | None,
    evidence_refs: list[str],
) -> AgenticDeRepoWritableSurfaceHardeningRegister:
    root_origin_ids = [
        f"descriptor:{descriptor.repo_writable_surface_descriptor_id}",
        f"lease:{lease.repo_write_lease_id}",
        f"admission:{admission.repo_write_surface_admission_id}",
        f"communication_egress:{communication_egress.communication_egress_id}",
        f"continuation:{continuation_refresh_decision.refresh_decision_id}",
        f"policy:{V64C_FROZEN_POLICY_REF}",
    ]
    if restoration is not None:
        root_origin_ids.append(f"restoration:{restoration.repo_write_restoration_id}")
    if reintegration is not None:
        root_origin_ids.append(f"reintegration:{reintegration.repo_write_reintegration_report_id}")

    selected_kind_summary: str | None = None
    selected_kind_parts: list[str] = []
    if restoration is not None:
        selected_kind_parts.append(f"restoration_status={restoration.restoration_status}")
    if reintegration is not None:
        selected_kind_parts.append(f"reintegration_status={reintegration.reintegration_status}")
    if restoration is not None:
        selected_kind_parts.insert(0, "write_kind=create_new")
    if selected_kind_parts:
        selected_kind_summary = "; ".join(selected_kind_parts)

    has_optional_upstream_basis = restoration is not None or reintegration is not None
    recommended_outcome: str = (
        "candidate_for_later_writable_surface_hardening"
        if has_optional_upstream_basis
        else "keep_warning_only"
    )
    evidence_basis_summary = (
        "shipped V64-A selected writable-surface descriptor, admitted repo write lease, and "
        "exact target admission"
        + (
            " plus shipped V64-B restoration-local lineage"
            if restoration is not None
            else " without shipped V64-B restoration-local lineage selected"
        )
        + (
            " plus shipped V64-B reintegration lineage"
            if reintegration is not None
            else " without shipped V64-B reintegration lineage selected"
        )
        + (
            " over the same exact shipped V60-B continuation basis and shipped V61-A "
            "communication lineage under one explicit frozen V64-C policy anchor"
        )
    )
    verdict_basis_summary = (
        "the same exact admitted writable surface and target remained preserved, optional "
        "restoration and reintegration refs stayed posture-consistent where selected, preserved "
        "local_write/create_new semantics stayed explicit, and one frozen V64-C policy anchor "
        "kept provenance and non-independence dedup explicit without minting live writable, "
        "repo-admin, shell, execute, dispatch, worker, connector, or remote authority"
    )
    field_origin_tags = {
        "selected_writable_surface_identity_summary": "prior_artifact",
        "selected_target_path_summary": "prior_artifact",
        "target_admission_verdict": "prior_artifact",
        "selected_write_effect_or_restoration_kind_summary_or_none": "current_turn_derived",
        "preserved_write_semantics_summary": "prior_artifact",
        "latest_continuation_basis_selection_summary": "current_turn_derived",
        "frozen_policy_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "verdict_basis_summary": "current_turn_derived",
        "recommended_outcome": "current_turn_derived",
    }
    field_dependence_tags = {
        "selected_writable_surface_identity_summary": [
            descriptor.repo_writable_surface_descriptor_id,
        ],
        "selected_target_path_summary": [admission.repo_write_surface_admission_id],
        "target_admission_verdict": [admission.repo_write_surface_admission_id],
        "selected_write_effect_or_restoration_kind_summary_or_none": [
            ref
            for ref in [
                restoration.repo_write_restoration_id if restoration is not None else None,
                (
                    reintegration.repo_write_reintegration_report_id
                    if reintegration is not None
                    else None
                ),
            ]
            if ref is not None
        ],
        "preserved_write_semantics_summary": [
            (
                restoration.repo_write_restoration_id
                if restoration is not None
                else lease.repo_write_lease_id
            )
        ],
        "latest_continuation_basis_selection_summary": [
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
        ],
        "frozen_policy_ref": [],
        "evidence_basis_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            lease.repo_write_lease_id,
            admission.repo_write_surface_admission_id,
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
            *root_origin_ids,
        ],
        "verdict_basis_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            admission.repo_write_surface_admission_id,
            continuation_refresh_decision.refresh_decision_id,
            *root_origin_ids,
        ],
        "recommended_outcome": [
            descriptor.repo_writable_surface_descriptor_id,
            admission.repo_write_surface_admission_id,
            continuation_refresh_decision.refresh_decision_id,
            V64C_FROZEN_POLICY_REF,
        ],
    }
    entry = AgenticDeRepoWritableSurfaceHardeningEntry(
        repo_writable_surface_descriptor_ref=descriptor.repo_writable_surface_descriptor_id,
        repo_write_lease_ref=lease.repo_write_lease_id,
        repo_write_surface_admission_ref=admission.repo_write_surface_admission_id,
        repo_write_restoration_ref_or_none=(
            restoration.repo_write_restoration_id if restoration is not None else None
        ),
        repo_write_reintegration_ref_or_none=(
            reintegration.repo_write_reintegration_report_id if reintegration is not None else None
        ),
        selected_write_effect_or_restoration_kind_summary_or_none=selected_kind_summary,
        preserved_write_semantics_summary=(
            restoration.preserved_write_semantics_summary
            if restoration is not None
            else lease.preserved_write_semantics_summary
        ),
        selected_writable_surface_identity_summary=descriptor.selected_surface_identity_summary,
        selected_target_path_summary=admission.selected_target_path_summary,
        target_admission_verdict=admission.admission_verdict,
        latest_continuation_basis_ref_or_equivalent=continuation_refresh_decision.refresh_decision_id,
        latest_continuation_basis_selection_summary=(
            "latest shipped V60-B refresh decision remains the selected continuation basis for "
            "the exact shipped writable-surface lineage only"
        ),
        selected_hardening_target_surface=(
            "shipped_v64a_v64b_writable_surface_lineage_over_one_exact_admitted_repo_path_only"
        ),
        frozen_policy_ref=V64C_FROZEN_POLICY_REF,
        evidence_basis_summary=evidence_basis_summary,
        verdict_basis_summary=verdict_basis_summary,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated writable-surface descriptor, lease, admission, restoration, "
            "reintegration, continuation, communication, and policy artifacts remain "
            "non-independent writable-surface hardening support"
        ),
        recommended_outcome=recommended_outcome,
        rationale=(
            "the exact shipped V64-A/V64-B writable-surface lineage now carries admitted "
            "surface and target posture, optional shipped restoration-local basis, preserved "
            "local_write/create_new semantics, and one frozen V64-C advisory policy anchor, "
            "so it is a valid later path-level writable-surface hardening candidate without "
            "minting live surface selection, lease issuance, target admission, restoration, "
            "repo-admin, shell, execute, dispatch, worker, connector, or remote authority"
            if has_optional_upstream_basis
            else "without optional shipped restoration or reintegration exemplar basis, V64-C "
            "keeps the current advisory posture only and may not overread restoration-local "
            "evidence"
        ),
        reason_codes=(
            [
                "admitted_writable_surface_lineage_consumed",
                "optional_upstream_basis_posture_consistent",
                "preserved_local_write_create_new_only",
                "selected_kind_summary_explicit",
                "committed_artifacts_outrank_narrative_docs",
                "path_level_only",
                "extensional_replayable_policy",
                "lineage_root_dedup_applied",
                "candidate_non_entitling_and_non_escalating",
                "later_lock_required_for_scope",
                "no_live_mutation_in_v64c",
                "non_generalizing_by_default",
            ]
            if has_optional_upstream_basis
            else [
                "admitted_writable_surface_lineage_consumed",
                "optional_upstream_basis_absent_no_overread",
                "preserved_local_write_create_new_only",
                "committed_artifacts_outrank_narrative_docs",
                "path_level_only",
                "extensional_replayable_policy",
                "lineage_root_dedup_applied",
                "keep_warning_only_retains_current_advisory_posture_only",
                "no_live_mutation_in_v64c",
                "non_generalizing_by_default",
            ]
        ),
        evidence_refs=evidence_refs,
    )
    return AgenticDeRepoWritableSurfaceHardeningRegister(
        target_arc=V64C_TARGET_ARC,
        target_path=V64C_TARGET_PATH,
        optional_upstream_basis_consistency_fails_closed=True,
        baseline_checker_version=V64C_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


def run_agentic_de_repo_writable_surface_hardening_v64c(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v64a_repo_writable_surface_descriptor_path: Path = (
        DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH
    ),
    v64a_repo_write_lease_path: Path = DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    v64a_repo_write_surface_admission_path: Path = DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    v64b_repo_write_restoration_path: Path | None = DEFAULT_V64B_REPO_WRITE_RESTORATION_PATH,
    v64b_repo_write_reintegration_path: Path | None = DEFAULT_V64B_REPO_WRITE_REINTEGRATION_PATH,
    lane_drift_path: Path = DEFAULT_V64C_LANE_DRIFT_PATH,
    v64a_evidence_path: Path = DEFAULT_V64A_EVIDENCE_PATH,
    v64b_evidence_path: Path = DEFAULT_V64B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeRepoWritableSurfaceHardeningRegister:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if not raw_root.exists():
        raise FileNotFoundError(f"repository root not found: {raw_root}")
    if raw_root.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V64-C repo writable surface hardening"
        )
    root = raw_root.resolve()

    path_args: dict[str, Path | None] = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v64a_repo_writable_surface_descriptor_path": v64a_repo_writable_surface_descriptor_path,
        "v64a_repo_write_lease_path": v64a_repo_write_lease_path,
        "v64a_repo_write_surface_admission_path": v64a_repo_write_surface_admission_path,
        "v64b_repo_write_restoration_path": v64b_repo_write_restoration_path,
        "v64b_repo_write_reintegration_path": v64b_repo_write_reintegration_path,
        "lane_drift_path": lane_drift_path,
        "v64a_evidence_path": v64a_evidence_path,
        "v64b_evidence_path": v64b_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        if path is None:
            continue
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v64c_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v64c_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v64a_evidence_payload(
        _load_json_object(resolved_paths["v64a_evidence_path"], error_label="V64-A evidence")
    )
    _validate_v64b_evidence_payload(
        _load_json_object(resolved_paths["v64b_evidence_path"], error_label="V64-B evidence")
    )

    normalized_target_relative_path, _surface_path, _target_path, _surface_class = (
        _assert_v64a_surface_and_target_canonical_membership(
            repo_root_path=root,
            target_relative_path=target_relative_path,
        )
    )
    canonical_target_relative_path = normalized_target_relative_path.as_posix()

    continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    communication_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    surface_authority_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    ingress_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    descriptor = load_repo_writable_surface_descriptor(
        resolved_paths["v64a_repo_writable_surface_descriptor_path"]
    )
    lease = load_repo_write_lease_record(resolved_paths["v64a_repo_write_lease_path"])
    admission = load_repo_write_surface_admission_record(
        resolved_paths["v64a_repo_write_surface_admission_path"]
    )
    restoration = (
        load_repo_write_restoration_record(resolved_paths["v64b_repo_write_restoration_path"])
        if "v64b_repo_write_restoration_path" in resolved_paths
        else None
    )
    reintegration = (
        load_repo_write_reintegration_report(
            resolved_paths["v64b_repo_write_reintegration_path"]
        )
        if "v64b_repo_write_reintegration_path" in resolved_paths
        else None
    )

    _validate_v64c_consumed_surfaces(
        continuation_refresh_decision=continuation_refresh_decision,
        communication_ingress=communication_ingress,
        surface_authority_descriptor=surface_authority_descriptor,
        ingress_interpretation=ingress_interpretation,
        communication_egress=communication_egress,
        descriptor=descriptor,
        lease=lease,
        admission=admission,
        restoration=restoration,
        reintegration=reintegration,
        target_relative_path=canonical_target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64a_repo_writable_surface_descriptor_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v64a_repo_write_lease_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64a_repo_write_surface_admission_path"],
        ),
    ]
    if "v64b_repo_write_restoration_path" in resolved_paths:
        evidence_refs.append(
            _render_input_ref(
                repo_root_path=root,
                path=resolved_paths["v64b_repo_write_restoration_path"],
            )
        )
    if "v64b_repo_write_reintegration_path" in resolved_paths:
        evidence_refs.append(
            _render_input_ref(
                repo_root_path=root,
                path=resolved_paths["v64b_repo_write_reintegration_path"],
            )
        )
    evidence_refs.extend(
        [
            _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
            _render_input_ref(repo_root_path=root, path=resolved_paths["v64a_evidence_path"]),
            _render_input_ref(repo_root_path=root, path=resolved_paths["v64b_evidence_path"]),
        ]
    )
    return _build_v64c_repo_writable_surface_hardening_register(
        continuation_refresh_decision=continuation_refresh_decision,
        communication_egress=communication_egress,
        descriptor=descriptor,
        lease=lease,
        admission=admission,
        restoration=restoration,
        reintegration=reintegration,
        evidence_refs=evidence_refs,
    )


def _validate_v65a_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_ingress: AgenticDeCommunicationIngressPacket,
    surface_authority_descriptor: AgenticDeSurfaceAuthorityDescriptor,
    ingress_interpretation: AgenticDeIngressInterpretationRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    admission: AgenticDeRepoWriteSurfaceAdmissionRecord,
    hardening_register: AgenticDeRepoWritableSurfaceHardeningRegister,
    worker_topology: WorkerDelegationTopology,
    released_worker_topology: WorkerDelegationTopology,
    target_relative_path: str,
) -> None:
    expected_path = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    expected_target_summary = (
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
    )
    (
        expected_surface_class,
        _surface_relative,
        expected_surface_identity_summary,
        _inclusion_summary,
        _exclusion_summary,
    ) = _derive_v64a_surface_selection(target_relative_path=target_relative_path)

    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V65-A requires the shipped V60-B continuation refresh surface")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V65-A requires the shipped V60-B continuation policy anchor")
    if continuation_refresh_decision.selected_next_path_summary_or_none != expected_path:
        raise ValueError("V65-A requires the shipped exact V60 selected downstream path")

    if (
        communication_ingress.target_arc != V61A_TARGET_ARC
        or communication_ingress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V65-A requires the shipped V61-A communication ingress surface")
    if (
        surface_authority_descriptor.target_arc != V61A_TARGET_ARC
        or surface_authority_descriptor.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V65-A requires the shipped V61-A surface authority descriptor")
    if (
        ingress_interpretation.target_arc != V61A_TARGET_ARC
        or ingress_interpretation.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V65-A requires the shipped V61-A ingress interpretation surface")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V65-A requires the shipped V61-A communication egress surface")
    if communication_ingress.selected_api_route_ref_or_equivalent != V61A_SELECTED_API_ROUTE:
        raise ValueError("V65-A requires the shipped exact resident V61-A ingress seam")
    if communication_ingress.selected_runtime_message_method != V61A_SELECTED_RUNTIME_METHOD:
        raise ValueError("V65-A requires the shipped exact resident V61-A runtime method")
    if communication_ingress.surface_class != V61A_SELECTED_SURFACE_CLASS:
        raise ValueError("V65-A requires the shipped exact resident V61-A surface class")
    if (
        surface_authority_descriptor.communication_ingress_ref
        != communication_ingress.communication_ingress_id
    ):
        raise ValueError("V65-A surface descriptor must bind the shipped V61-A ingress packet")
    if (
        ingress_interpretation.communication_ingress_ref
        != communication_ingress.communication_ingress_id
    ):
        raise ValueError("V65-A ingress interpretation must bind the shipped V61-A ingress packet")
    if (
        ingress_interpretation.surface_authority_descriptor_ref
        != surface_authority_descriptor.surface_authority_descriptor_id
    ):
        raise ValueError("V65-A ingress interpretation must bind the shipped V61-A descriptor")
    if (
        ingress_interpretation.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError(
            "V65-A ingress interpretation must preserve the shipped V60-B continuation basis"
        )
    if (
        communication_egress.ingress_interpretation_ref
        != ingress_interpretation.ingress_interpretation_id
    ):
        raise ValueError("V65-A communication egress must bind the shipped V61-A interpretation")
    if (
        communication_egress.latest_v60_continuation_basis_ref
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError(
            "V65-A communication egress must preserve the shipped V60-B continuation basis"
        )
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V65-A requires the shipped exact resident V61-A egress seam")

    if descriptor.target_arc != V64A_TARGET_ARC or descriptor.target_path != V64A_TARGET_PATH:
        raise ValueError("V65-A requires the shipped V64-A writable-surface descriptor")
    if lease.target_arc != V64A_TARGET_ARC or lease.target_path != V64A_TARGET_PATH:
        raise ValueError("V65-A requires the shipped V64-A repo write lease")
    if admission.target_arc != V64A_TARGET_ARC or admission.target_path != V64A_TARGET_PATH:
        raise ValueError("V65-A requires the shipped V64-A repo write surface admission")
    if descriptor.selected_surface_class != expected_surface_class:
        raise ValueError("V65-A requires the shipped V64-A selected surface class")
    if descriptor.selected_surface_identity_summary != expected_surface_identity_summary:
        raise ValueError("V65-A requires the shipped V64-A selected writable surface only")
    if lease.writable_surface_descriptor_ref != descriptor.repo_writable_surface_descriptor_id:
        raise ValueError("V65-A lease must bind the shipped V64-A writable-surface descriptor")
    if admission.writable_surface_descriptor_ref != descriptor.repo_writable_surface_descriptor_id:
        raise ValueError("V65-A admission must bind the shipped V64-A writable-surface descriptor")
    if admission.repo_write_lease_ref != lease.repo_write_lease_id:
        raise ValueError("V65-A admission must bind the shipped V64-A repo write lease")
    if lease.lease_verdict != "admitted":
        raise ValueError("V65-A requires the shipped admitted V64-A repo write lease")
    if admission.admission_verdict != "admitted":
        raise ValueError("V65-A requires the shipped admitted V64-A target admission")
    if admission.selected_target_path_summary != expected_target_summary:
        raise ValueError("V65-A requires the shipped exact V64-A admitted target path")

    if (
        hardening_register.target_arc != V64C_TARGET_ARC
        or hardening_register.target_path != V64C_TARGET_PATH
    ):
        raise ValueError("V65-A requires the shipped V64-C hardening register")
    if (
        hardening_register.advisory_only is not True
        or hardening_register.candidate_only is not True
    ):
        raise ValueError("V65-A requires the shipped advisory-only V64-C posture")
    if hardening_register.changes_live_behavior_by_default is not False:
        raise ValueError("V65-A requires the shipped non-live-mutating V64-C posture")
    if len(hardening_register.entries) != 1:
        raise ValueError("V65-A requires exactly one shipped V64-C hardening entry")
    hardening_entry = hardening_register.entries[0]
    if (
        hardening_entry.repo_writable_surface_descriptor_ref
        != descriptor.repo_writable_surface_descriptor_id
    ):
        raise ValueError("V65-A V64-C hardening entry must bind the shipped V64-A descriptor")
    if hardening_entry.repo_write_lease_ref != lease.repo_write_lease_id:
        raise ValueError("V65-A V64-C hardening entry must bind the shipped V64-A lease")
    if (
        hardening_entry.repo_write_surface_admission_ref
        != admission.repo_write_surface_admission_id
    ):
        raise ValueError("V65-A V64-C hardening entry must bind the shipped V64-A admission")
    if (
        hardening_entry.latest_continuation_basis_ref_or_equivalent
        != continuation_refresh_decision.refresh_decision_id
    ):
        raise ValueError("V65-A V64-C hardening entry must preserve the shipped V60-B basis")
    if hardening_entry.selected_target_path_summary != admission.selected_target_path_summary:
        raise ValueError("V65-A V64-C hardening entry must preserve the shipped exact target")
    if hardening_entry.target_admission_verdict != "admitted":
        raise ValueError("V65-A requires the shipped admitted V64-C target posture")
    if "local_write/create_new" not in hardening_entry.preserved_write_semantics_summary:
        raise ValueError("V65-A requires the shipped preserved local_write/create_new posture")

    if worker_topology.schema != WORKER_DELEGATION_TOPOLOGY_SCHEMA:
        raise ValueError("V65-A requires the released V48-E worker delegation topology schema")
    if worker_topology.handoff_result != "completed":
        raise ValueError("V65-A requires the released completed V48-E worker topology")
    if worker_topology.topology_scope_posture != "one_parent_one_child_one_edge_only":
        raise ValueError("V65-A requires the released single-edge V48-E worker topology")
    if worker_topology.authority_relation_posture != "same_compiled_boundary_no_widening":
        raise ValueError("V65-A requires the released no-widening V48-E authority relation")
    if worker_topology.parent_role_kind != "supervisor":
        raise ValueError("V65-A requires the released supervisor role in V48-E topology")
    if worker_topology.child_role_kind != "worker":
        raise ValueError("V65-A requires the released worker role in V48-E topology")
    if worker_topology.delegation_edge_kind != "supervisor_to_worker":
        raise ValueError("V65-A requires the released supervisor_to_worker V48-E edge")
    if worker_topology.supporting_diagnostic_families:
        raise ValueError("V65-A requires the released diagnostic-clean V48-E worker topology")
    exact_v48e_lineage_fields = (
        ("worker_delegation_topology_id", "released exact V48-E topology lineage"),
        ("delegation_edge_id", "released exact V48-E delegation edge lineage"),
        ("repo_ref", "released exact V48-E repository lineage"),
        ("snapshot_id", "released exact V48-E snapshot lineage"),
        ("snapshot_sha256", "released exact V48-E snapshot hash"),
        ("parent_compiled_binding_ref", "released exact V48-E parent compiled binding"),
        ("child_compiled_binding_ref", "released exact V48-E child compiled binding"),
        (
            "parent_worker_boundary_conformance_report_ref",
            "released exact V48-E parent boundary conformance lineage",
        ),
        (
            "child_worker_boundary_conformance_report_ref",
            "released exact V48-E child boundary conformance lineage",
        ),
    )
    for field_name, description in exact_v48e_lineage_fields:
        if getattr(worker_topology, field_name) != getattr(released_worker_topology, field_name):
            raise ValueError(f"V65-A requires the {description}")


def _build_v65a_delegated_worker_export_packet(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
    lease: AgenticDeRepoWriteLeaseRecord,
    admission: AgenticDeRepoWriteSurfaceAdmissionRecord,
    hardening_register: AgenticDeRepoWritableSurfaceHardeningRegister,
    worker_topology: WorkerDelegationTopology,
    evidence_refs: list[str],
) -> AgenticDeDelegatedWorkerExportPacket:
    hardening_entry = hardening_register.entries[0]
    root_origin_ids = [
        f"descriptor:{descriptor.repo_writable_surface_descriptor_id}",
        f"lease:{lease.repo_write_lease_id}",
        f"admission:{admission.repo_write_surface_admission_id}",
        f"hardening:{hardening_register.register_id}",
        f"continuation:{continuation_refresh_decision.refresh_decision_id}",
        f"communication_egress:{communication_egress.communication_egress_id}",
        f"worker_topology:{worker_topology.worker_delegation_topology_id}",
        f"policy:{V65A_FROZEN_POLICY_REF}",
    ]
    field_origin_tags = {
        "selected_export_scope_summary": "current_turn_derived",
        "exported_work_membership_basis_summary": "current_turn_derived",
        "selected_target_or_patch_or_artifact_summary": "prior_artifact",
        "repo_writable_surface_descriptor_ref": "prior_artifact",
        "repo_write_lease_ref": "prior_artifact",
        "repo_write_surface_admission_ref": "prior_artifact",
        "worker_carrier_basis_ref_or_equivalent": "prior_artifact",
        "selected_worker_topology_basis_ref_or_equivalent": "prior_artifact",
        "worker_carrier_lineage_summary": "current_turn_derived",
        "selected_worker_topology_summary": "current_turn_derived",
        "consumed_continuation_basis_summary": "current_turn_derived",
        "consumed_communication_basis_summary_or_none": "current_turn_derived",
        "preserved_write_semantics_summary": "prior_artifact",
        "export_verdict": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "selected_export_scope_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            admission.repo_write_surface_admission_id,
            worker_topology.worker_delegation_topology_id,
        ],
        "exported_work_membership_basis_summary": [
            descriptor.repo_writable_surface_descriptor_id,
            admission.repo_write_surface_admission_id,
            hardening_register.register_id,
        ],
        "selected_target_or_patch_or_artifact_summary": [admission.repo_write_surface_admission_id],
        "repo_writable_surface_descriptor_ref": [descriptor.repo_writable_surface_descriptor_id],
        "repo_write_lease_ref": [lease.repo_write_lease_id],
        "repo_write_surface_admission_ref": [admission.repo_write_surface_admission_id],
        "worker_carrier_basis_ref_or_equivalent": [worker_topology.child_compiled_binding_ref],
        "selected_worker_topology_basis_ref_or_equivalent": [
            worker_topology.worker_delegation_topology_id
        ],
        "worker_carrier_lineage_summary": [
            worker_topology.child_compiled_binding_ref,
            worker_topology.child_worker_boundary_conformance_report_ref,
            worker_topology.worker_delegation_topology_id,
        ],
        "selected_worker_topology_summary": [worker_topology.worker_delegation_topology_id],
        "consumed_continuation_basis_summary": [continuation_refresh_decision.refresh_decision_id],
        "consumed_communication_basis_summary_or_none": [
            communication_egress.communication_egress_id
        ],
        "preserved_write_semantics_summary": [hardening_entry.hardening_id],
        "export_verdict": [
            descriptor.repo_writable_surface_descriptor_id,
            admission.repo_write_surface_admission_id,
            worker_topology.worker_delegation_topology_id,
            V65A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [V65A_FROZEN_POLICY_REF],
    }
    return AgenticDeDelegatedWorkerExportPacket(
        target_arc=V65A_TARGET_ARC,
        target_path=V65A_TARGET_PATH,
        selected_export_scope_summary=(
            "one shipped V64-A selected writable surface over the same exact admitted "
            "target only is exportable here under one released V48-E worker carrier "
            "lineage and one selected worker topology only"
        ),
        exported_work_membership_basis_summary=(
            "exported-work membership reuses the shipped V64-A canonical target-membership "
            "and admitted target basis plus shipped V64-C shaping-only drift guard context; "
            "no extra local paths may be laundered into worker-side scope"
        ),
        selected_target_or_patch_or_artifact_summary=admission.selected_target_path_summary,
        repo_writable_surface_descriptor_ref=descriptor.repo_writable_surface_descriptor_id,
        repo_write_lease_ref=lease.repo_write_lease_id,
        repo_write_surface_admission_ref=admission.repo_write_surface_admission_id,
        worker_carrier_basis_ref_or_equivalent=worker_topology.child_compiled_binding_ref,
        selected_worker_topology_basis_ref_or_equivalent=(
            worker_topology.worker_delegation_topology_id
        ),
        worker_carrier_lineage_summary=(
            "released V48-E child compiled binding and child worker-boundary conformance "
            "remain the only admitted worker-carrier lineage here"
        ),
        selected_worker_topology_summary=(
            "released V48-E completed supervisor_to_worker topology remains the only "
            "selected worker topology here with no fan-out or alternate topology widening"
        ),
        consumed_continuation_basis_summary=(
            "shipped V60-B refresh decision remains the selected continuation basis for the "
            "same exact exported local target only"
        ),
        consumed_communication_basis_summary_or_none=(
            "shipped V61-A communication egress lineage may contextualize export posture and "
            "answer routing only; it does not mint export authority"
        ),
        preserved_write_semantics_summary=hardening_entry.preserved_write_semantics_summary,
        export_verdict="admitted_for_export",
        frozen_policy_anchor_ref=V65A_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated writable-surface, hardening, continuation, communication, worker "
            "topology, and policy artifacts remain non-independent delegated export support"
        ),
        reason_codes=[
            "shipped_v64a_local_writable_basis_consumed",
            "shipped_v64c_hardening_context_consumed_as_shaping_only",
            "released_v48e_worker_topology_basis_consumed",
            "single_worker_carrier_only",
            "single_selected_worker_topology_only",
            "preserved_local_write_create_new_only",
            "typed_replayable_export_only",
            "delegated_export_not_reconciliation_or_dispatch_or_execute",
            "no_all_repo_multi_worker_connector_or_remote_authority",
        ],
        evidence_refs=[
            descriptor.repo_writable_surface_descriptor_id,
            lease.repo_write_lease_id,
            admission.repo_write_surface_admission_id,
            hardening_register.register_id,
            worker_topology.worker_delegation_topology_id,
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_delegated_worker_export_v65a(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_ingress_path: Path = DEFAULT_V61A_COMMUNICATION_INGRESS_PATH,
    v61a_surface_authority_descriptor_path: Path = DEFAULT_V61A_SURFACE_AUTHORITY_DESCRIPTOR_PATH,
    v61a_ingress_interpretation_path: Path = DEFAULT_V61A_INGRESS_INTERPRETATION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v64a_repo_writable_surface_descriptor_path: Path = (
        DEFAULT_V64A_REPO_WRITABLE_SURFACE_DESCRIPTOR_PATH
    ),
    v64a_repo_write_lease_path: Path = DEFAULT_V64A_REPO_WRITE_LEASE_PATH,
    v64a_repo_write_surface_admission_path: Path = DEFAULT_V64A_REPO_WRITE_SURFACE_ADMISSION_PATH,
    v64c_repo_writable_surface_hardening_path: Path = (
        DEFAULT_V64C_REPO_WRITABLE_SURFACE_HARDENING_PATH
    ),
    v48e_worker_delegation_topology_path: Path = DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH,
    lane_drift_path: Path = DEFAULT_V65A_LANE_DRIFT_PATH,
    v64c_evidence_path: Path = DEFAULT_V64C_EVIDENCE_PATH,
    v48e_evidence_path: Path = DEFAULT_V48E_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeDelegatedWorkerExportPacket:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if not raw_root.exists():
        raise FileNotFoundError(f"repository root not found: {raw_root}")
    if raw_root.is_symlink():
        raise ValueError("repository root may not be a symlink for V65-A delegated worker export")
    root = raw_root.resolve()

    path_args = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_ingress_path": v61a_communication_ingress_path,
        "v61a_surface_authority_descriptor_path": v61a_surface_authority_descriptor_path,
        "v61a_ingress_interpretation_path": v61a_ingress_interpretation_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v64a_repo_writable_surface_descriptor_path": v64a_repo_writable_surface_descriptor_path,
        "v64a_repo_write_lease_path": v64a_repo_write_lease_path,
        "v64a_repo_write_surface_admission_path": v64a_repo_write_surface_admission_path,
        "v64c_repo_writable_surface_hardening_path": v64c_repo_writable_surface_hardening_path,
        "v48e_worker_delegation_topology_path": v48e_worker_delegation_topology_path,
        "lane_drift_path": lane_drift_path,
        "v64c_evidence_path": v64c_evidence_path,
        "v48e_evidence_path": v48e_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v65a_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate

    _validate_v65a_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v64c_evidence_payload_for_v65a(
        _load_json_object(resolved_paths["v64c_evidence_path"], error_label="V64-C evidence")
    )
    _validate_v48e_evidence_payload_for_v65a(
        _load_json_object(resolved_paths["v48e_evidence_path"], error_label="V48-E evidence")
    )

    normalized_target_relative_path, _surface_path, _target_path, _surface_class = (
        _assert_v64a_surface_and_target_canonical_membership(
            repo_root_path=root,
            target_relative_path=target_relative_path,
        )
    )
    canonical_target_relative_path = normalized_target_relative_path.as_posix()

    continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    communication_ingress = load_communication_ingress_packet(
        resolved_paths["v61a_communication_ingress_path"]
    )
    surface_authority_descriptor = load_surface_authority_descriptor(
        resolved_paths["v61a_surface_authority_descriptor_path"]
    )
    ingress_interpretation = load_ingress_interpretation_record(
        resolved_paths["v61a_ingress_interpretation_path"]
    )
    communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    descriptor = load_repo_writable_surface_descriptor(
        resolved_paths["v64a_repo_writable_surface_descriptor_path"]
    )
    lease = load_repo_write_lease_record(resolved_paths["v64a_repo_write_lease_path"])
    admission = load_repo_write_surface_admission_record(
        resolved_paths["v64a_repo_write_surface_admission_path"]
    )
    hardening_register = load_repo_writable_surface_hardening_register(
        resolved_paths["v64c_repo_writable_surface_hardening_path"]
    )
    worker_topology = load_worker_delegation_topology(
        resolved_paths["v48e_worker_delegation_topology_path"]
    )
    released_worker_topology = load_worker_delegation_topology(
        DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH
    )

    _validate_v65a_consumed_surfaces(
        continuation_refresh_decision=continuation_refresh_decision,
        communication_ingress=communication_ingress,
        surface_authority_descriptor=surface_authority_descriptor,
        ingress_interpretation=ingress_interpretation,
        communication_egress=communication_egress,
        descriptor=descriptor,
        lease=lease,
        admission=admission,
        hardening_register=hardening_register,
        worker_topology=worker_topology,
        released_worker_topology=released_worker_topology,
        target_relative_path=canonical_target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_ingress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_surface_authority_descriptor_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_ingress_interpretation_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64a_repo_writable_surface_descriptor_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v64a_repo_write_lease_path"]),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64a_repo_write_surface_admission_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v64c_repo_writable_surface_hardening_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v48e_worker_delegation_topology_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v64c_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v48e_evidence_path"]),
    ]
    return _build_v65a_delegated_worker_export_packet(
        continuation_refresh_decision=continuation_refresh_decision,
        communication_egress=communication_egress,
        descriptor=descriptor,
        lease=lease,
        admission=admission,
        hardening_register=hardening_register,
        worker_topology=worker_topology,
        evidence_refs=evidence_refs,
    )


def _validate_v65b_consumed_surfaces(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    export_packet: AgenticDeDelegatedWorkerExportPacket,
    worker_conformance: WorkerBoundaryConformanceReport,
    worker_topology: WorkerDelegationTopology,
    released_worker_topology: WorkerDelegationTopology,
    target_relative_path: str,
    worker_conformance_input_ref: str,
) -> None:
    expected_target_summary = (
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
    )
    if export_packet.target_arc != V65A_TARGET_ARC or export_packet.target_path != V65A_TARGET_PATH:
        raise ValueError("V65-B requires the shipped V65-A delegated worker export surface")
    if export_packet.frozen_policy_anchor_ref != V65A_FROZEN_POLICY_REF:
        raise ValueError("V65-B requires the shipped V65-A export policy anchor")
    if export_packet.export_verdict != "admitted_for_export":
        raise ValueError("V65-B requires the shipped admitted V65-A export verdict")
    if export_packet.selected_target_or_patch_or_artifact_summary != expected_target_summary:
        raise ValueError("V65-B requires the shipped exact V65-A exported target summary")
    if "local_write/create_new" not in export_packet.preserved_write_semantics_summary:
        raise ValueError("V65-B requires the shipped preserved local_write/create_new posture")
    if (
        continuation_refresh_decision.target_arc != V60B_TARGET_ARC
        or continuation_refresh_decision.target_path != V60B_TARGET_PATH
    ):
        raise ValueError("V65-B requires the shipped V60-B continuation refresh surface")
    if continuation_refresh_decision.frozen_policy_anchor_ref != V60B_FROZEN_POLICY_REF:
        raise ValueError("V65-B requires the shipped V60-B continuation policy anchor")
    if (
        communication_egress.target_arc != V61A_TARGET_ARC
        or communication_egress.target_path != V61A_TARGET_PATH
    ):
        raise ValueError("V65-B requires the shipped V61-A communication egress surface")
    if communication_egress.frozen_policy_anchor_ref != V61A_FROZEN_POLICY_REF:
        raise ValueError("V65-B requires the shipped V61-A egress policy anchor")
    if communication_egress.selected_egress_surface_ref != V61A_SELECTED_API_ROUTE:
        raise ValueError("V65-B requires the shipped exact resident V61-A egress seam")
    if (
        export_packet.worker_carrier_basis_ref_or_equivalent
        != worker_topology.child_compiled_binding_ref
    ):
        raise ValueError("V65-B export packet must preserve the released child worker carrier")
    if (
        export_packet.selected_worker_topology_basis_ref_or_equivalent
        != worker_topology.worker_delegation_topology_id
    ):
        raise ValueError("V65-B export packet must preserve the released selected worker topology")
    if worker_topology.schema != WORKER_DELEGATION_TOPOLOGY_SCHEMA:
        raise ValueError("V65-B requires the released V48-E worker delegation topology schema")
    exact_v48e_lineage_fields = (
        "worker_delegation_topology_id",
        "delegation_edge_id",
        "repo_ref",
        "snapshot_id",
        "snapshot_sha256",
        "parent_compiled_binding_ref",
        "child_compiled_binding_ref",
        "parent_worker_boundary_conformance_report_ref",
        "child_worker_boundary_conformance_report_ref",
    )
    for field_name in exact_v48e_lineage_fields:
        if getattr(worker_topology, field_name) != getattr(released_worker_topology, field_name):
            raise ValueError(f"V65-B requires the released exact V48-E {field_name}")
    if worker_conformance.schema != WORKER_BOUNDARY_CONFORMANCE_REPORT_SCHEMA:
        raise ValueError("V65-B requires the released V48-D worker boundary conformance schema")
    if worker_conformance.overall_judgment != "conformant":
        raise ValueError("V65-B requires a conformant released worker result basis")
    if worker_conformance.supporting_diagnostic_ids:
        raise ValueError("V65-B requires a diagnostic-clean released worker result basis")
    if worker_conformance.compiled_binding_ref != worker_topology.child_compiled_binding_ref:
        raise ValueError("V65-B worker result basis must match the selected worker carrier")
    if (
        worker_conformance.compiled_binding_ref
        != export_packet.worker_carrier_basis_ref_or_equivalent
    ):
        raise ValueError("V65-B worker result basis must match the shipped V65-A worker carrier")
    if worker_conformance.repo_ref != worker_topology.repo_ref:
        raise ValueError("V65-B worker result basis must match the selected worker topology repo")
    if worker_conformance.snapshot_id != worker_topology.snapshot_id:
        raise ValueError(
            "V65-B worker result basis must match the selected worker topology snapshot"
        )
    if worker_conformance.snapshot_sha256 != worker_topology.snapshot_sha256:
        raise ValueError(
            "V65-B worker result basis must match the selected worker topology snapshot hash"
        )
    if worker_conformance.worker_subject_ref != worker_topology.child_worker_subject_ref:
        raise ValueError("V65-B worker result basis must match the selected worker subject")
    if worker_conformance.worker_subject_kind != worker_topology.child_worker_subject_kind:
        raise ValueError("V65-B worker result basis must match the selected worker subject kind")
    if worker_conformance.worker_scope_posture != "single_worker_only":
        raise ValueError("V65-B requires the released single-worker result posture")


def _build_v65b_delegated_worker_reconciliation_report(
    *,
    continuation_refresh_decision: AgenticDeContinuationRefreshDecisionRecord,
    communication_egress: AgenticDeCommunicationEgressPacket,
    export_packet: AgenticDeDelegatedWorkerExportPacket,
    worker_conformance: WorkerBoundaryConformanceReport,
    worker_topology: WorkerDelegationTopology,
    evidence_refs: list[str],
) -> AgenticDeDelegatedWorkerReconciliationReport:
    root_origin_ids = [
        f"export:{export_packet.delegated_worker_export_packet_id}",
        f"worker_result:{worker_conformance.worker_boundary_conformance_report_id}",
        f"worker_topology:{worker_topology.worker_delegation_topology_id}",
        f"continuation:{continuation_refresh_decision.refresh_decision_id}",
        f"communication_egress:{communication_egress.communication_egress_id}",
        f"policy:{V65B_FROZEN_POLICY_REF}",
    ]
    field_origin_tags = {
        "delegated_worker_export_packet_ref": "prior_artifact",
        "worker_result_or_conformance_basis_ref_or_equivalent": "prior_artifact",
        "selected_worker_result_or_conformance_kind_summary": "current_turn_derived",
        "worker_carrier_basis_ref_or_equivalent": "prior_artifact",
        "selected_worker_topology_basis_ref_or_equivalent": "prior_artifact",
        "selected_export_scope_summary": "prior_artifact",
        "exported_work_membership_basis_summary": "prior_artifact",
        "selected_target_or_patch_or_artifact_summary": "prior_artifact",
        "reconciliation_basis_summary": "current_turn_derived",
        "consumed_continuation_basis_summary": "current_turn_derived",
        "consumed_communication_basis_summary_or_none": "current_turn_derived",
        "preserved_write_semantics_summary": "prior_artifact",
        "reconciliation_status": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
    }
    field_dependence_tags = {
        "delegated_worker_export_packet_ref": [export_packet.delegated_worker_export_packet_id],
        "worker_result_or_conformance_basis_ref_or_equivalent": [
            worker_conformance.worker_boundary_conformance_report_id
        ],
        "selected_worker_result_or_conformance_kind_summary": [
            worker_conformance.worker_boundary_conformance_report_id
        ],
        "worker_carrier_basis_ref_or_equivalent": [worker_topology.child_compiled_binding_ref],
        "selected_worker_topology_basis_ref_or_equivalent": [
            worker_topology.worker_delegation_topology_id
        ],
        "selected_export_scope_summary": [export_packet.delegated_worker_export_packet_id],
        "exported_work_membership_basis_summary": [export_packet.delegated_worker_export_packet_id],
        "selected_target_or_patch_or_artifact_summary": [
            export_packet.delegated_worker_export_packet_id
        ],
        "reconciliation_basis_summary": [
            export_packet.delegated_worker_export_packet_id,
            worker_conformance.worker_boundary_conformance_report_id,
            worker_topology.worker_delegation_topology_id,
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
            V65B_FROZEN_POLICY_REF,
        ],
        "consumed_continuation_basis_summary": [continuation_refresh_decision.refresh_decision_id],
        "consumed_communication_basis_summary_or_none": [
            communication_egress.communication_egress_id
        ],
        "preserved_write_semantics_summary": [export_packet.delegated_worker_export_packet_id],
        "reconciliation_status": [
            export_packet.delegated_worker_export_packet_id,
            worker_conformance.worker_boundary_conformance_report_id,
        ],
        "frozen_policy_anchor_ref": [V65B_FROZEN_POLICY_REF],
    }
    return AgenticDeDelegatedWorkerReconciliationReport(
        target_arc=V65B_TARGET_ARC,
        target_path=V65B_TARGET_PATH,
        delegated_worker_export_packet_ref=export_packet.delegated_worker_export_packet_id,
        worker_result_or_conformance_basis_ref_or_equivalent=(
            worker_conformance.worker_boundary_conformance_report_id
        ),
        selected_worker_result_or_conformance_kind_summary=(
            "worker_result_or_conformance_kind=boundary_conformance_report; "
            f"overall_judgment={worker_conformance.overall_judgment}"
        ),
        worker_carrier_basis_ref_or_equivalent=export_packet.worker_carrier_basis_ref_or_equivalent,
        selected_worker_topology_basis_ref_or_equivalent=(
            export_packet.selected_worker_topology_basis_ref_or_equivalent
        ),
        selected_export_scope_summary=export_packet.selected_export_scope_summary,
        exported_work_membership_basis_summary=export_packet.exported_work_membership_basis_summary,
        selected_target_or_patch_or_artifact_summary=(
            export_packet.selected_target_or_patch_or_artifact_summary
        ),
        reconciliation_basis_summary=(
            "one shipped V65-A delegated export packet reconciled one released worker boundary "
            "conformance lineage back to the same exported scope, the same selected worker "
            "carrier and topology, and the same shipped V60-B and V61-A basis under one frozen "
            "V65-B policy anchor"
        ),
        consumed_continuation_basis_summary=(
            "shipped V60-B refresh decision remains the selected continuation basis for the same "
            "delegated export lineage only"
        ),
        consumed_communication_basis_summary_or_none=(
            "shipped V61-A communication egress lineage may contextualize reconciliation posture "
            "only; it does not mint fresh local, export, or worker authority"
        ),
        preserved_write_semantics_summary=export_packet.preserved_write_semantics_summary,
        reconciliation_status="reconciled_to_export_lineage",
        frozen_policy_anchor_ref=V65B_FROZEN_POLICY_REF,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; shipped delegated export, released worker result, released worker topology, "
            "continuation, communication, and policy artifacts remain non-independent "
            "reconciliation support rather than fresh authority"
        ),
        reason_codes=[
            "shipped_v65a_export_lineage_consumed",
            "released_v48d_worker_result_basis_consumed",
            "released_v48e_worker_topology_basis_consumed",
            "same_exported_scope_only",
            "same_worker_carrier_and_topology_only",
            "preserved_local_write_create_new_only",
            "typed_replayable_reconciliation_only",
            "reconciliation_not_fresh_local_export_or_worker_authority",
            "no_all_repo_shell_execute_dispatch_multi_worker_connector_or_remote_authority",
        ],
        evidence_refs=[
            export_packet.delegated_worker_export_packet_id,
            worker_conformance.worker_boundary_conformance_report_id,
            worker_topology.worker_delegation_topology_id,
            continuation_refresh_decision.refresh_decision_id,
            communication_egress.communication_egress_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_delegated_worker_reconciliation_v65b(
    *,
    repo_root_path: Path | None = None,
    v60b_continuation_refresh_decision_path: Path = DEFAULT_V60B_CONTINUATION_REFRESH_DECISION_PATH,
    v61a_communication_egress_path: Path = DEFAULT_V61A_COMMUNICATION_EGRESS_PATH,
    v65a_delegated_worker_export_path: Path = DEFAULT_V65A_DELEGATED_WORKER_EXPORT_PATH,
    worker_boundary_conformance_path: Path = DEFAULT_V65B_WORKER_BOUNDARY_CONFORMANCE_PATH,
    v48e_worker_delegation_topology_path: Path = DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH,
    lane_drift_path: Path = DEFAULT_V65B_LANE_DRIFT_PATH,
    v65a_evidence_path: Path = DEFAULT_V65A_EVIDENCE_PATH,
    v48d_evidence_path: Path = DEFAULT_V48D_EVIDENCE_PATH,
    v48e_evidence_path: Path = DEFAULT_V48E_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeDelegatedWorkerReconciliationReport:
    raw_root = repo_root(anchor=Path(__file__)) if repo_root_path is None else repo_root_path
    if not raw_root.exists():
        raise FileNotFoundError(f"repository root not found: {raw_root}")
    if raw_root.is_symlink():
        raise ValueError(
            "repository root may not be a symlink for V65-B delegated worker reconciliation"
        )
    root = raw_root.resolve()
    path_args = {
        "v60b_continuation_refresh_decision_path": v60b_continuation_refresh_decision_path,
        "v61a_communication_egress_path": v61a_communication_egress_path,
        "v65a_delegated_worker_export_path": v65a_delegated_worker_export_path,
        "worker_boundary_conformance_path": worker_boundary_conformance_path,
        "v48e_worker_delegation_topology_path": v48e_worker_delegation_topology_path,
        "lane_drift_path": lane_drift_path,
        "v65a_evidence_path": v65a_evidence_path,
        "v48d_evidence_path": v48d_evidence_path,
        "v48e_evidence_path": v48e_evidence_path,
    }
    resolved_paths: dict[str, Path] = {}
    for field_name, path in path_args.items():
        candidate = _resolve_path(repo_root_path=root, path=path)
        _assert_v65b_repo_local_input_path(
            repo_root_path=root,
            candidate=candidate,
            field_name=field_name,
        )
        resolved_paths[field_name] = candidate
    _validate_v65b_lane_drift_record(load_lane_drift_record(resolved_paths["lane_drift_path"]))
    _validate_v65a_evidence_payload_for_v65b(
        _load_json_object(resolved_paths["v65a_evidence_path"], error_label="V65-A evidence")
    )
    _validate_v48d_evidence_payload_for_v65b(
        _load_json_object(resolved_paths["v48d_evidence_path"], error_label="V48-D evidence")
    )
    _validate_v48e_evidence_payload_for_v65a(
        _load_json_object(resolved_paths["v48e_evidence_path"], error_label="V48-E evidence")
    )
    normalized_target_relative_path, _surface_path, _target_path, _surface_class = (
        _assert_v64a_surface_and_target_canonical_membership(
            repo_root_path=root,
            target_relative_path=target_relative_path,
        )
    )
    canonical_target_relative_path = normalized_target_relative_path.as_posix()
    continuation_refresh_decision = load_continuation_refresh_decision_record(
        resolved_paths["v60b_continuation_refresh_decision_path"]
    )
    communication_egress = load_communication_egress_packet(
        resolved_paths["v61a_communication_egress_path"]
    )
    export_packet = load_delegated_worker_export_packet(
        resolved_paths["v65a_delegated_worker_export_path"]
    )
    worker_conformance = load_worker_boundary_conformance_report(
        resolved_paths["worker_boundary_conformance_path"]
    )
    worker_topology = load_worker_delegation_topology(
        resolved_paths["v48e_worker_delegation_topology_path"]
    )
    released_worker_topology = load_worker_delegation_topology(
        DEFAULT_V48E_WORKER_DELEGATION_TOPOLOGY_PATH
    )
    worker_conformance_input_ref = _render_input_ref(
        repo_root_path=root, path=resolved_paths["worker_boundary_conformance_path"]
    )
    _validate_v65b_consumed_surfaces(
        continuation_refresh_decision=continuation_refresh_decision,
        communication_egress=communication_egress,
        export_packet=export_packet,
        worker_conformance=worker_conformance,
        worker_topology=worker_topology,
        released_worker_topology=released_worker_topology,
        target_relative_path=canonical_target_relative_path,
        worker_conformance_input_ref=worker_conformance_input_ref,
    )
    evidence_refs = [
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v60b_continuation_refresh_decision_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v61a_communication_egress_path"],
        ),
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v65a_delegated_worker_export_path"],
        ),
        worker_conformance_input_ref,
        _render_input_ref(
            repo_root_path=root,
            path=resolved_paths["v48e_worker_delegation_topology_path"],
        ),
        _render_input_ref(repo_root_path=root, path=resolved_paths["lane_drift_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v65a_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v48d_evidence_path"]),
        _render_input_ref(repo_root_path=root, path=resolved_paths["v48e_evidence_path"]),
    ]
    return _build_v65b_delegated_worker_reconciliation_report(
        continuation_refresh_decision=continuation_refresh_decision,
        communication_egress=communication_egress,
        export_packet=export_packet,
        worker_conformance=worker_conformance,
        worker_topology=worker_topology,
        evidence_refs=evidence_refs,
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


def render_task_residual_refresh_payload(
    task_residual_refresh: AgenticDeTaskResidualRefreshPacket,
) -> str:
    return (
        json.dumps(task_residual_refresh.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"
    )


def render_loop_state_ledger_payload(loop_state_ledger: AgenticDeLoopStateLedger) -> str:
    return json.dumps(loop_state_ledger.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_continuation_decision_payload(
    decision: AgenticDeContinuationDecisionRecord,
) -> str:
    return json.dumps(decision.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_continuation_refresh_decision_payload(
    decision: AgenticDeContinuationRefreshDecisionRecord,
) -> str:
    return json.dumps(decision.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_continuation_hardening_payload(
    register: AgenticDeContinuationHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_communication_ingress_payload(
    packet: AgenticDeCommunicationIngressPacket,
) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_surface_authority_descriptor_payload(
    descriptor: AgenticDeSurfaceAuthorityDescriptor,
) -> str:
    return json.dumps(descriptor.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_ingress_interpretation_payload(
    record: AgenticDeIngressInterpretationRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_communication_egress_payload(
    packet: AgenticDeCommunicationEgressPacket,
) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_bridge_office_binding_payload(
    record: AgenticDeBridgeOfficeBindingRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_message_rewitness_gate_payload(
    record: AgenticDeMessageRewitnessGateRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_connector_admission_payload(record: AgenticDeConnectorAdmissionRecord) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_external_assistant_ingress_bridge_payload(
    packet: AgenticDeExternalAssistantIngressBridgePacket,
) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_external_assistant_egress_bridge_payload(
    packet: AgenticDeExternalAssistantEgressBridgePacket,
) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_remote_operator_session_payload(
    record: AgenticDeRemoteOperatorSessionRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_remote_operator_view_payload(packet: AgenticDeRemoteOperatorViewPacket) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_remote_operator_response_payload(
    record: AgenticDeRemoteOperatorResponseRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_remote_operator_control_bridge_payload(
    packet: AgenticDeRemoteOperatorControlBridgePacket,
) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_remote_operator_hardening_payload(
    register: AgenticDeRemoteOperatorHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_repo_writable_surface_descriptor_payload(
    descriptor: AgenticDeRepoWritableSurfaceDescriptor,
) -> str:
    return json.dumps(descriptor.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_repo_write_lease_payload(lease: AgenticDeRepoWriteLeaseRecord) -> str:
    return json.dumps(lease.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_repo_write_surface_admission_payload(
    record: AgenticDeRepoWriteSurfaceAdmissionRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_repo_write_restoration_payload(
    record: AgenticDeRepoWriteRestorationRecord,
) -> str:
    return json.dumps(record.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_repo_write_reintegration_payload(
    report: AgenticDeRepoWriteReintegrationReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_repo_writable_surface_hardening_payload(
    register: AgenticDeRepoWritableSurfaceHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_delegated_worker_export_payload(
    packet: AgenticDeDelegatedWorkerExportPacket,
) -> str:
    return json.dumps(packet.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_delegated_worker_reconciliation_payload(
    report: AgenticDeDelegatedWorkerReconciliationReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_governed_communication_hardening_payload(
    register: AgenticDeGovernedCommunicationHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_connector_bridge_hardening_payload(
    register: AgenticDeConnectorBridgeHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


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
