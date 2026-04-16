# LOCKED_CONTINUATION_vNEXT_PLUS170

## Status

Bounded starter lock draft for `V62-A` (step-1 starter).

## Authority Layer

lock

## Family / Slice

- family: `V62`
- slice: `V62-A`
- branch-local execution target: `arc/v62-r1`

## Purpose

Freeze the bounded connector-admission and external-assistant ingress-bridge posture
for `V62-A` so the repo can admit one exact connector path into the already shipped
`V61` governed communication membrane without letting connector transport, connector
identity, snapshot visibility, connector exposure, or raw upstream external-assistant
output become ambient authority.

`vNext+170` authorizes docs plus the first `V62-A` implementation path over existing
repo-owned packages and thin backend seams, but not human-via-connector law, outbound
connector bridge law, remote-operator UX law, repo-bound writable authority, replay /
resume widening, execute widening, dispatch widening, product/UI rollout as
authority, advisory-to-live promotion, or hidden-cognition governance.

In `vNext+170`, the new `V62-A` outputs are connector-admission and ingress-bridge
surfaces only. They do not change task-charter semantics, task-residual semantics,
loop-state semantics, continuation semantics, governed communication law,
bridge-office law, rewitness law, continuity semantics, or exit behavior by default.

## Instantiated Here

- `V62-A` instantiates only one bounded connector starter seam:
  - existing repo-owned packages:
    - `adeu_agentic_de`
    - `urm_runtime`
  - existing API/backend surfaces as needed:
    - `apps/api/src/adeu_api/`
    - `apps/api/scripts/`
  - one explicit `V61-C` to `V62-A` lane handoff via `agentic_de_lane_drift_record@1`
  - one exact admitted connector path only:
    - connector snapshot create route:
      - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot`
    - connector snapshot get route:
      - `apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}`
    - connector snapshot provider:
      - `codex`
    - connector snapshot execution mode:
      - `live`
  - one selected connector-carried principal only:
    - `external_assistant`
    - `human_via_connector` deferred
  - one consumed shipped continuation lineage only:
    - the shipped exact `V60` continuation lineage over the same continuity-bound
      `local_write/create_new` exemplar
  - one consumed shipped governed communication lineage only:
    - communication ingress packet
    - surface-authority descriptor
    - ingress interpretation record
    - no outbound `V62` bridge packet yet
  - the same selected downstream live action class only:
    - `local_write`
  - the same selected downstream write kind only:
    - `create_new`
  - the same declared continuity root only:
    - `artifacts/agentic_de/v59/workspace_continuity/`
  - the same exact downstream target only:
    - `runtime/reference_patch_candidate.diff`
  - two new bounded starter surfaces only:
    - `agentic_de_connector_admission_record@1`
    - `agentic_de_external_assistant_ingress_bridge_packet@1`
  - one explicit non-equivalence law:
    - connector transport is not authority
    - connector identity is context, not permission
    - snapshot visibility is not admission by itself
    - connector exposure is not admission by itself
    - raw connector payload is not native witness
    - raw connector payload is not charter compilation
    - raw connector payload is not continuation mutation
    - raw connector payload is not act authority
    - external assistant ingress bridge is not bridge office
    - external assistant ingress bridge is not repo-write authority
  - one explicit ordering law:
    - `V62-A` is downstream of shipped `V61`
    - it does not replace shipped `V60` continuation law
    - connector admission consumes shipped connector snapshot / exposure facts rather
      than replacing them
    - ingress bridge in `V62-A` consumes shipped `V61-A` communication law rather
      than replacing it
    - bridge-office or rewitness consumption is not selected in `V62-A`
    - `V61-B` remains prior-family evidence only in this starter slice rather than a
      required live ingress basis
    - human-via-connector semantics remain deferred
    - outbound external assistant bridge remains deferred to `V62-B`
    - remote/operator UX remains deferred to `V63`
  - one explicit posture law:
    - connector admission remains typed and replayable
    - ingress bridge remains typed and replayable
    - same selected connector identity facts plus same selected snapshot / exposure /
      freshness basis plus same frozen policy yields the same admission verdict
    - same admitted connector basis plus same external assistant payload facts plus
      same consumed `V61` communication basis plus same frozen policy yields the same
      ingress bridge packet
    - missing or stale connector basis fails closed
    - only `external_assistant` principal posture is selected in this slice
    - no result in this slice becomes native witness, charter mutation,
      continuation mutation, bridge office, act authority, or repo-write authority
      by default
- `V62-A` must consume the shipped `V58`, `V59`, `V60`, and `V61` surfaces by
  default rather than reopen them.

## Required Deliverables / Exit Conditions

- one explicit `V61-C` to `V62-A` lane handoff record
- one typed connector admission record over the selected connector snapshot seam only
- one typed external assistant ingress bridge packet over that same admitted
  connector path only
- deterministic reference fixtures and schema export for the two `V62-A` surfaces
- one thin starter runner over existing backend seams only
- tests that prove:
  - connector admission remains explicit, replayable, and fail-closed on missing or
    stale basis
  - external-assistant principal selection remains explicit
  - human-via-connector semantics do not land in this slice
  - ingress bridge remains explicit and replayable
  - raw connector payload does not become witness, charter, continuation, or act
    authority
  - bridge basis consumes shipped `V61` communication law rather than inventing
    connector-native interpretation law
  - broader connector-fleet, remote-operator, repo, execute, and dispatch law do not
    land in this slice

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS170.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+170",
  "target_path": "V62-A",
  "slice": "V62-A",
  "family": "V62",
  "branch_local_execution_target": "arc/v62-r1",
  "target_scope": "one_bounded_connector_admission_and_external_assistant_ingress_bridge_slice_over_one_exact_connector_snapshot_path_and_one_shipped_v61_governed_communication_lineage_only",
  "implementation_packages": [
    "adeu_agentic_de",
    "urm_runtime"
  ],
  "api_surfaces": [
    "apps/api/src/adeu_api",
    "apps/api/scripts"
  ],
  "prerequisite_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS169.md",
  "prerequisite_decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS169.md",
  "prerequisite_assessment_doc": "docs/ASSESSMENT_vNEXT_PLUS169_EDGES.md",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_FAMILY_v0.md",
  "family_support_mapping_doc": "docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62_IMPLEMENTATION_MAPPING_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62A_IMPLEMENTATION_MAPPING_v0.md",
  "admitted_shaping_inputs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v45.md",
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_FAMILY_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_FAMILY_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_V61_IMPLEMENTATION_MAPPING_v0.md",
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_FAMILY_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "prior_lane_handoff_record_required": true,
  "prior_lane_handoff_record_schema": "agentic_de_lane_drift_record@1",
  "required_prior_lane_evidence_surfaces": [
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
    "artifacts/agent_harness/v168/evidence_inputs/v61b_bridge_office_rewitness_evidence_v168.json",
    "artifacts/agent_harness/v169/evidence_inputs/v61c_governed_communication_hardening_evidence_v169.json"
  ],
  "selected_record_shapes": [
    "agentic_de_communication_ingress_packet@1",
    "agentic_de_surface_authority_descriptor@1",
    "agentic_de_ingress_interpretation_record@1",
    "agentic_de_connector_admission_record@1",
    "agentic_de_external_assistant_ingress_bridge_packet@1"
  ],
  "selected_connector_snapshot_create_route_for_v62a": "apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot",
  "selected_connector_snapshot_get_route_for_v62a": "apps/api/src/adeu_api/urm_routes.py:/connectors/snapshot/{snapshot_id}",
  "selected_connector_provider_for_v62a": "codex_only",
  "selected_connector_snapshot_execution_mode_for_v62a": "live_only",
  "selected_connector_principal_for_v62a": "external_assistant_only",
  "selected_consumed_v61_communication_seam_for_v62a": "shipped_v61_resident_send_lineage_only",
  "selected_consumed_v61_resident_send_surface": "urm_copilot_send_path_only",
  "selected_consumed_v61_api_route": "apps/api/src/adeu_api/urm_routes.py:/copilot/send",
  "selected_consumed_v61_runtime_message_method": "copilot.user_message_only",
  "selected_downstream_action_class_for_v62a": "local_write",
  "selected_downstream_write_kind_for_v62a": "create_new",
  "selected_continuity_root_for_v62a": "artifacts/agentic_de/v59/workspace_continuity/",
  "selected_target_relative_path": "runtime/reference_patch_candidate.diff",
  "required_connector_admission_axes": [
    "connector_snapshot_ref",
    "connector_snapshot_hash",
    "capability_snapshot_ref",
    "connector_provider_class",
    "connector_identity_facts",
    "connector_exposure_basis_ref_or_summary",
    "connector_route_basis_summary",
    "freshness_basis_summary",
    "selected_connector_principal_class",
    "frozen_policy_anchor_ref",
    "admission_verdict",
    "field_origin_tags",
    "field_dependence_tags",
    "root_origin_dedup_summary",
    "reason_codes"
  ],
  "required_ingress_bridge_axes": [
    "connector_admission_ref",
    "selected_connector_principal_class",
    "external_assistant_payload_facts",
    "consumed_communication_ingress_ref",
    "consumed_surface_authority_descriptor_ref",
    "consumed_ingress_interpretation_ref",
    "latest_continuation_basis_ref_or_equivalent",
    "frozen_policy_anchor_ref",
    "field_origin_tags",
    "field_dependence_tags",
    "root_origin_dedup_summary",
    "reason_codes"
  ],
  "connector_admission_must_be_typed_and_replayable": true,
  "same_selected_connector_identity_facts_plus_same_selected_snapshot_exposure_facts_plus_same_freshness_basis_plus_same_frozen_policy_yields_same_connector_admission_verdict": true,
  "connector_admission_verdicts": [
    "admitted",
    "rejected",
    "stale_basis",
    "unknown_basis",
    "withheld_by_policy"
  ],
  "missing_or_stale_connector_snapshot_or_exposure_basis_fails_closed_in_v62a": true,
  "external_assistant_ingress_bridge_must_be_typed_and_replayable": true,
  "same_admitted_connector_basis_plus_same_external_assistant_payload_facts_plus_same_consumed_v61_communication_basis_plus_same_frozen_policy_yields_same_ingress_bridge_packet": true,
  "ingress_bridge_consumes_v61a_basis_only_in_v62a": true,
  "v61b_bridge_office_or_rewitness_basis_not_selected_for_v62a_ingress": true,
  "connector_transport_not_authority": true,
  "connector_identity_not_permission": true,
  "snapshot_visibility_not_admission_by_itself": true,
  "connector_exposure_not_admission_by_itself": true,
  "raw_connector_payload_not_native_witness_by_default": true,
  "raw_connector_payload_not_charter_compilation": true,
  "raw_connector_payload_not_continuation_mutation": true,
  "raw_connector_payload_not_act_authority": true,
  "external_assistant_ingress_bridge_not_bridge_office": true,
  "external_assistant_ingress_bridge_not_repo_write_authority": true,
  "human_via_connector_selected_for_v62a": false,
  "connector_egress_bridge_selected_for_v62a": false,
  "connector_advisory_hardening_selected_for_v62a": false,
  "path_level_non_generalization_required_for_v62a": true,
  "selected_connector_path_may_not_generalize_by_default_into_human_via_connector_law": true,
  "selected_connector_path_may_not_generalize_by_default_into_remote_operator_law": true,
  "selected_connector_path_may_not_generalize_by_default_into_broader_connector_fleet_trust_law": true,
  "selected_connector_path_may_not_generalize_by_default_into_bridge_office_family_law": true,
  "selected_connector_path_may_not_generalize_by_default_into_repo_or_execution_authority_law": true,
  "remote_operator_law_selected_for_v62a": false,
  "repo_authority_widening_selected_for_v62a": false,
  "execute_widening_selected_for_v62a": false,
  "dispatch_widening_selected_for_v62a": false,
  "product_or_api_rollout_selected": false,
  "hidden_cognition_governance_selected": false
}
```

## Explicit Non-Goals

- no human-via-connector semantics under cover of `V62-A`
- no outbound connector bridge packet under cover of `V62-A`
- no connector advisory hardening under cover of `V62-A`
- no connector-fleet widening
- no remote-operator widening
- no repo-bound writable-surface widening
- no execute widening
- no dispatch widening
- no product-surface rollout as authority
- no hidden-cognition or proxy-governance authority
