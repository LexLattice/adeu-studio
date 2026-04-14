# LOCKED_CONTINUATION_vNEXT_PLUS159

## Status

Bounded starter lock draft for `V58-B` (step-2 fill).

## Authority Layer

lock

## Family / Slice

- family: `V58`
- slice: `V58-B`
- branch-local execution target: `arc/v58-r2`

## Purpose

Freeze the bounded continuation posture for the `V58-B` live harness
restoration-state integration seam so the repo can bind one explicit compensating
restore over the shipped `V58-A` live-turn lineage and the shipped `V57-B`
restoration exemplar without silently widening `local_write` semantics, sandbox
authority, replay authority, repo write authority, delegated/external dispatch,
product/UI authority, or hidden-cognition governance.

`vNext+159` authorizes docs plus the first live restoration handoff / reintegration
implementation path over existing repo-owned packages and thin backend seams, but not
restoration-family widening, append-only restoration integration, broader repo cleanup
semantics, harness replay hardening, broader `local_write` coverage,
`local_reversible_execute`, stronger execute, delegated/external dispatch, product/UI
rollout as authority, or hidden-cognition governance.

In `vNext+159`, the new `V58-B` outputs are current-turn evidence-bearing surfaces
only. They do not change packet semantics, checkpoint semantics, ticket semantics,
selected `local_write` semantics, selected `V57-B` restoration semantics, selected
sandbox semantics, live-turn admission semantics, live-turn reintegration semantics,
diagnostics semantics, or exit behavior by default.

## Instantiated Here

- `V58-B` instantiates only one bounded live harness restoration-state seam:
  - existing repo-owned packages:
    - `adeu_agentic_de`
    - `urm_runtime`
  - existing API/backend surfaces as needed:
    - `apps/api/src/adeu_api/`
    - `apps/api/scripts/`
  - one explicit `V58-A` to `V58-B` lane handoff via
    `agentic_de_lane_drift_record@1`
  - one existing live session path only:
    - URM copilot session path
  - one selected live action class only:
    - `local_write`
  - one selected live write kind only:
    - `create_new`
  - the same designated local-effect sandbox root only:
    - `artifacts/agentic_de/v57/local_effect/`
  - one exact live restoration target only:
    - `runtime/reference_patch_candidate.diff`
  - one selected restoration exemplar only:
    - compensating restore of the shipped `V57-A` `create_new` artifact through
      shipped `V57-B`
  - two new bounded restore-state surfaces only:
    - `agentic_de_live_restoration_handoff_record@1`
    - `agentic_de_live_restoration_reintegration_report@1`
  - one starter restoration phase only:
    - restoration effect through shipped `V57-B`
  - one explicit non-equivalence law:
    - outer harness capability is necessary at most, never sufficient
    - `writes_allowed` is not a `V56` ticket
    - approval posture is not ticket-equivalent
    - transcript and event stream are not native witness
    - prior fixtures and closeout evidence are not current-turn restoration witness
  - one explicit restoration authority law:
    - restoration is a new live act, not ambient continuing authority
    - the original `V56` ticket is not ambient ongoing restoration authority
    - restoration must remain lineage-bound, evidence-bound, and bounded to the same
      exact compensating scope
  - one explicit restoration-time freshness law:
    - restoration remains same-session and same-turn only in this slice
    - restoration-time capability / approval posture must be re-snapshotted
    - mismatch or missing resnapshot fails closed
  - one explicit lineage-input law:
    - `action_ticket_ref` and prior reintegration refs are historical lineage inputs
      only
    - they support bounded compensating-scope derivation
    - they do not by themselves mint current-turn restoration entitlement
  - one narrow replay meaning only:
    - bounded recomputation and re-evaluation of the exact restoration event against
      the prior observed/restored lineage
    - not arbitrary prior live-action re-execution
    - the replay-law proof surface lives inside the live restoration reintegration
      report
- `V58-B` must consume the shipped `V56-A`, `V56-B`, `V56-C`, `V57-A`, `V57-B`,
  `V57-C`, and `V58-A` surfaces rather than reopen them:
  - packet / morph IR / interaction-contract / action-proposal reuse is the default
  - membrane-checkpoint / diagnostics / conformance reuse is the default
  - action-class taxonomy / runtime-state / action-ticket reuse is the default
  - local-effect observation / local-effect conformance / local-effect restoration
    reuse is the default
  - live-turn admission / handoff / reintegration reuse is the default
  - hardening outputs may be consumed only as shaping and drift-guard context, not as
    current-turn restoration entitlement
  - any fork of those surfaces requires one explicit
    `agentic_de_lane_drift_record@1` amendment path
- the seam remains bounded to one live restoration-state integration slice for
  `vNEXT_PLUS159`.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+159",
  "target_path": "V58-B",
  "slice": "V58-B",
  "family": "V58",
  "branch_local_execution_target": "arc/v58-r2",
  "target_scope": "one_bounded_live_harness_restoration_state_integration_slice_over_the_shipped_v58a_live_turn_bind_and_the_shipped_v57b_create_new_compensating_restore_path_only",
  "implementation_packages": [
    "adeu_agentic_de",
    "urm_runtime"
  ],
  "api_surfaces": [
    "apps/api/src/adeu_api",
    "apps/api/scripts"
  ],
  "prerequisite_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md",
  "prerequisite_decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS158.md",
  "prerequisite_assessment_doc": "docs/ASSESSMENT_vNEXT_PLUS158_EDGES.md",
  "governing_stack_consumption_mode": "consume_shipped_v56_v57_and_v58a_surfaces_plus_explicit_lane_drift_and_closed_shaping_inputs_only_without_hidden_cleanup_or_advisory_to_live_promotion",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md",
  "family_support_mapping_doc": "docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58B_IMPLEMENTATION_MAPPING_v0.md",
  "admitted_shaping_inputs": [
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_INTERACTION_GOVERNANCE_FAMILY_v0.md",
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LOCAL_EFFECT_HARDENING_FAMILY_v0.md",
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/support/ADEU_SCHEMA_META_GRAMMAR.md",
    "docs/support/AGENTIC_DE_TYPE_GRAMMAR.md",
    "docs/support/ODEU_MEMBRANE_ARCHITECTURE.md",
    "docs/support/ODEU AS A COUPLED SEMANTIC HYPERSPACE WITH LAWFUL MORPHISMS_v2.md",
    "docs/support/endogenous cross-lane alignment by coupled boundary subdynamics_2nd pass.md",
    "docs/support/endogenous cross-lane alignment by coupled boundary subdynamics_3rd pass.md",
    "docs/support/endogenous grounding. md",
    "docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md",
    "docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md"
  ],
  "admitted_shaping_input_set_closed_for_v58b": true,
  "later_support_or_lineage_artifacts_require_explicit_amendment_record": true,
  "prior_lane_handoff_record_required": true,
  "prior_lane_handoff_record_schema": "agentic_de_lane_drift_record@1",
  "required_prior_lane_evidence_surfaces": [
    "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
    "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
    "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
    "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
    "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
    "artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json",
    "artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json",
    "packages/adeu_agentic_de/tests/fixtures/v57b/reference_agentic_de_local_effect_restoration_record.json",
    "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_live_turn_admission_record.json",
    "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_live_turn_handoff_record.json",
    "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_live_turn_reintegration_report.json"
  ],
  "selected_record_shapes": [
    "agentic_de_domain_packet@1",
    "agentic_de_morph_ir@1",
    "agentic_de_interaction_contract@1",
    "agentic_de_action_proposal@1",
    "agentic_de_membrane_checkpoint@1",
    "agentic_de_morph_diagnostics@1",
    "agentic_de_conformance_report@1",
    "agentic_de_lane_drift_record@1",
    "agentic_de_action_class_taxonomy@1",
    "agentic_de_runtime_state@1",
    "agentic_de_action_ticket@1",
    "agentic_de_local_effect_observation_record@1",
    "agentic_de_local_effect_conformance_report@1",
    "agentic_de_local_effect_restoration_record@1",
    "agentic_de_live_turn_admission_record@1",
    "agentic_de_live_turn_handoff_record@1",
    "agentic_de_live_turn_reintegration_report@1",
    "agentic_de_live_restoration_handoff_record@1",
    "agentic_de_live_restoration_reintegration_report@1"
  ],
  "selected_live_session_surface_for_v58b": "urm_copilot_session_path_only",
  "selected_live_action_class_for_v58b": "local_write",
  "selected_live_action_class_reused_from_v56b": true,
  "selected_live_action_class_interpretation_closed_for_v58b": true,
  "selected_live_action_class_semantic_repartition_forbidden_by_default": true,
  "selected_local_write_kind_for_v58b": "create_new",
  "selected_local_write_kind_closed_for_v58b": true,
  "selected_observed_effect_surface_for_v58b": "v57a_create_new_observation_only",
  "selected_restoration_surface_for_v58b": "v57b_create_new_compensating_restore_only",
  "selected_restoration_surface_interpretation_closed_for_v58b": true,
  "selected_restoration_surface_semantic_repartition_forbidden_by_default": true,
  "designated_local_effect_sandbox_root": "artifacts/agentic_de/v57/local_effect/",
  "selected_target_relative_path": "runtime/reference_patch_candidate.diff",
  "fresh_sandbox_semantics_reused_from_v57a": true,
  "live_turn_bind_reused_from_v58a": true,
  "outer_harness_capability_necessary_but_not_sufficient": true,
  "outer_writes_allowed_not_equivalent_to_v56_ticket": true,
  "approval_posture_not_ticket_equivalent": true,
  "transcript_and_event_stream_not_native_witness": true,
  "prior_fixtures_and_closeout_evidence_not_current_turn_restoration_witness": true,
  "explicit_restoration_handoff_required": true,
  "restoration_is_new_live_act_not_ambient_authority": true,
  "original_ticket_not_ambient_ongoing_restoration_authority": true,
  "same_session_and_same_turn_restoration_continuation_required": true,
  "restoration_time_capability_and_approval_resnapshot_required": true,
  "restoration_time_session_capability_snapshot_required": true,
  "restoration_time_approval_posture_snapshot_required": true,
  "restoration_time_capability_mismatch_or_missing_resnapshot_fails_closed": true,
  "action_ticket_ref_and_prior_reintegration_ref_are_historical_lineage_inputs_only": true,
  "historical_lineage_refs_do_not_by_themselves_mint_restoration_entitlement": true,
  "restoration_entitlement_mode_for_v58b": "lineage_bound_current_turn_evidence_bound_bounded_compensating_scope_derivation_only",
  "restoration_requires_explicit_bounded_compensating_scope_match_or_fail_closed": true,
  "positive_restoration_reintegration_requires_declared_current_turn_witness": true,
  "positive_restoration_reintegration_requires_witness_basis_or_certificate_ref": true,
  "handoff_and_reintegration_origin_tags_required": true,
  "root_origin_dedup_required_for_current_turn_support": true,
  "replay_mode_for_v58b": "bounded_recomputation_and_re_evaluation_of_the_exact_restoration_event_against_the_prior_observed_and_restored_lineage_only",
  "replay_law_proof_surface_embedded_in_live_restoration_reintegration_report": true,
  "higher_arity_contract_not_selected_for_v58b": true,
  "required_live_restoration_handoff_axes": [
    "turn_admission_ref",
    "turn_handoff_ref",
    "prior_reintegration_ref",
    "restoration_time_session_capability_snapshot",
    "restoration_time_approval_posture_snapshot",
    "restoration_time_continuation_verdict",
    "restoration_record_ref",
    "action_ticket_ref",
    "bounded_compensating_scope_derivation_summary",
    "target_relative_path",
    "selected_restoration_scope",
    "field_origin_tags",
    "field_dependence_tags",
    "root_origin_ids"
  ],
  "required_live_restoration_reintegration_axes": [
    "turn_admission_ref",
    "live_restoration_handoff_ref",
    "restoration_record_ref",
    "restoration_effect_summary",
    "restoration_reintegration_status",
    "reason_codes",
    "restoration_reintegration_witness_basis_summary",
    "restoration_reintegration_certificate_ref_or_equivalent",
    "replay_law_proof_summary",
    "field_origin_tags",
    "field_dependence_tags",
    "root_origin_dedup_summary",
    "six_lane_closeout_posture"
  ],
  "allowed_v58b_reintegration_outcomes": [
    "reintegrated",
    "blocked",
    "residualized",
    "not_evaluable_yet"
  ],
  "forbidden_v58b_outcomes": [
    "hidden_cleanup_now",
    "append_restore_now",
    "broader_write_now",
    "dispatch_now",
    "stronger_execute_now",
    "hardening_now",
    "product_authority_now"
  ],
  "product_or_ui_rollout_selected": false,
  "delegated_or_external_dispatch_selected": false,
  "local_reversible_execute_selected": false,
  "stronger_execute_selected": false,
  "restoration_family_widening_selected": false,
  "governs_hidden_cognition": false,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v41.md",
    "docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_FAMILY_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS158.md",
    "docs/ASSESSMENT_vNEXT_PLUS158_EDGES.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v41.md"
}
```

## Required Deliverables

The first `V58-B` release should add exactly these live restoration-state surfaces:

- one explicit `V58-A` to `V58-B` lane-drift/amendment record fixture
- one bounded live restoration handoff record:
  - `agentic_de_live_restoration_handoff_record@1`
- one bounded live restoration reintegration report:
  - `agentic_de_live_restoration_reintegration_report@1`
- one explicit reuse path over the shipped `V58-A` admission / handoff /
  reintegration surfaces
- one explicit reuse path over the shipped `V57-B` restoration surface
- one explicit restoration authority law only:
  - restoration is a new live act
  - the original ticket is not ambient restoration authority
  - restoration is lawful only when one bounded compensating scope can be derived and
    matched fail-closed from the prior observed/restored lineage
- one explicit restoration-time freshness law only:
  - restoration remains same-session and same-turn in this slice
  - restoration-time capability / approval posture must be re-snapshotted
  - mismatch or missing resnapshot fails closed
- one explicit lineage-input law only:
  - `action_ticket_ref` and prior reintegration refs remain historical lineage inputs
    only
  - they support bounded compensating-scope derivation
  - they do not by themselves mint restoration entitlement
- one explicit replay-law proof surface only:
  - bounded recomputation and re-evaluation of the exact restoration event against the
    prior observed/restored lineage only
  - embedded in the live restoration reintegration report
- one explicit handoff-axis law only:
  - restoration-time session capability snapshot is required
  - restoration-time approval posture snapshot is required
  - restoration-time continuation verdict is required
  - bounded compensating-scope derivation summary is required
- one selected restoration exemplar only:
  - compensating restore of the shipped `V57-A` `create_new` artifact under the exact
    designated sandbox root and target path
- one explicit current-turn witness law only:
  - positive restoration reintegration requires declared current-turn restoration
    witness basis or certificate ref
  - transcript / event stream remain observability only
  - prior fixtures / closeout evidence remain drift guards only
- tests proving:
  - restoration remains explicit harness state rather than hidden cleanup
  - restoration fails closed when the bounded compensating scope mismatches
  - restoration reuses one lawful `V58-A` admission / handoff / reintegration lineage
  - restoration stays inside the same designated sandbox root and target
  - replay remains bounded to the same exact restoration event
  - append-only restoration integration remains out of scope
  - no hardening output ships yet

## Explicit Non-Goals

- restoration-family widening
- append-only restoration integration
- a second `local_write` exemplar
- broader repo cleanup or hidden compensator semantics
- `local_reversible_execute`
- stronger execute
- delegated or external dispatch
- product/UI rollout as authority
- hidden-cognition governance

## Starter Validation

This docs-only starter bundle should be validated with:

```bash
make arc-start-check ARC=159
```
