# Draft ADEU Resident-Agent Continuation And Residual-Intent V60A Implementation Mapping v0

Status: support note for the `V60-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the first `V60`
slice should compile one typed starter seed intent into one bounded task charter,
derived residual, loop-state ledger, and continuation decision over the already
shipped exact continuity-bound exemplar path, without letting raw transcript semantics
or continuity state become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`

## Carry Forward Nearly As-Is

- shipped `V56-B` action-class, runtime-state, and ticket semantics
- shipped `V57-A` observation and local-effect conformance semantics
- shipped `V58-A` / `V58-B` live-turn admission / handoff / reintegration lineage
- shipped `V59-A` / `V59-B` continuity and continuity-safe restoration lineage over
  the selected path
- shipped `V59-C` advisory hardening posture as shaping input only
- the rule that prior continuity state is context at most, never sufficient authority
- the rule that `V56` ticket duration stays `single_step_local`

## Re-Author With Repo Alignment

`V60-A` should add exactly:

- `agentic_de_seed_intent_record@1`
- `agentic_de_task_charter_packet@1`
- `agentic_de_task_residual_packet@1`
- `agentic_de_loop_state_ledger@1`
- `agentic_de_continuation_decision_record@1`

`V60-A` should consume:

- one current URM copilot session path
- one explicit `agentic_de_lane_drift_record@1`
- shipped `V56-A` / `V56-B` packet / proposal / checkpoint / ticket surfaces
- shipped `V57-A` observation / local-effect conformance surfaces
- shipped `V58-A` / `V58-B` live-turn admission / handoff / reintegration surfaces
- shipped `V59-A` / `V59-B` continuity and continuity-safe restoration surfaces as
  selected downstream path lineage
- committed closeout evidence from shipped `V56` / `V57` / `V58` / `V59` lanes as
  drift guard only

Those prior committed artifacts should outrank narrative interpretation for drift
checking, but they should not count as starter seed intent, current-turn task law, or
current-turn continuation entitlement.

`V60-A` should keep the ordering explicit:

- starter seed intent is a typed bounded ingress record
- it does not replace shipped `V58` live admission
- continuation decision is a kernel output over already shipped lineage
- `continue_to_governed_act` still descends into the already ordered
  `V58` / `V56` / `V57` / `V59` governed act rather than reordering it
- `emit_governed_communication` is posture only here and does not mint `V61` packet
  law

## Starter Continuation Law

The starter continuation turn should make these laws explicit:

- starter seed intent must remain typed and non-chat-native
- starter seed intent should carry explicit provenance basis:
  - `seed_source_ref_or_equivalent`
  - or `seed_ingress_basis_summary`
- seed intent must remain replayable:
  - same selected seed-intent record
  - same frozen policy
  - same charter compilation result
- task charter compilation must remain typed and replayable:
  - same selected seed intent
  - same frozen policy
  - same task charter
- task charter is compiled bounded task law
- task charter is not raw user request echo
- `TaskResidual` must remain derived and replayable:
  - same selected derivation basis
  - same frozen policy
  - same residual posture
- `TaskResidual` is not human-authored law
- `TaskResidual` is not standing authority
- continuation decision must remain typed and replayable:
  - same selected evidence chain
  - same frozen policy
  - same continuation posture
- transcript, generic chat memory, and connector traffic remain non-entitling in this
  slice
- prior successful turn, prior ticket, and prior reintegration do not become standing
  continuation authority
- only `continue_to_governed_act` may descend into the shipped act ladder in this
  slice
- if `continue_to_governed_act`, the selected next path must equal the exact already
  shipped downstream `V59` continuity-bound exemplar only
- `emit_governed_communication` remains posture-only and deferred to `V61`
- broader communication law is not selected in this slice
- repo-bound writable authority is not selected in this slice
- replay / resume widening is not selected in this slice

The selected downstream path in this slice should remain exactly:

- live session path:
  - URM copilot session path already selected by `V58`
- action class:
  - `local_write`
- write kind:
  - `create_new`
- declared continuity root:
  - `artifacts/agentic_de/v59/workspace_continuity/`
- exact target centered on:
  - `runtime/reference_patch_candidate.diff`

## Required Axes

`agentic_de_seed_intent_record@1` should at minimum externalize:

- seed_intent_id
- structured_seed_intent_summary
- seed_source_ref_or_equivalent
- seed_ingress_basis_summary
- selected_downstream_path_summary
- declared_completion_test_summary
- declared_stop_condition_summary
- seed_source_class
- field_origin_tags
- field_dependence_tags

`agentic_de_task_charter_packet@1` should at minimum externalize:

- seed_intent_ref
- charter_id
- charter_scope_summary
- completion_test_summary
- stop_condition_summary
- required_imports_summary
- selected_downstream_path_summary
- frozen_policy_basis_ref
- charter_compilation_basis_summary
- field_origin_tags
- field_dependence_tags

`agentic_de_task_residual_packet@1` should at minimum externalize:

- task_charter_ref
- latest_live_turn_reintegration_ref_or_none
- latest_continuity_reintegration_ref_or_none
- current_frontier_summary
- open_obligation_summary
- blocker_summary
- open_approval_refs
- owed_communication_posture_summary
- residual_derivation_basis_summary
- field_origin_tags
- field_dependence_tags
- root_origin_ids

`agentic_de_loop_state_ledger@1` should at minimum externalize:

- task_charter_ref
- task_residual_ref
- resident_session_ref
- continuity_region_ref
- latest_live_turn_reintegration_ref_or_none
- latest_continuity_reintegration_ref_or_none
- open_approval_refs
- loop_prefix_identity
- field_origin_tags
- field_dependence_tags
- root_origin_ids

`agentic_de_continuation_decision_record@1` should at minimum externalize:

- loop_state_ledger_ref
- continuation_outcome
- continuation_reason_codes
- frozen_policy_anchor_ref
- evidence_basis_summary
- selected_next_path_summary
- field_origin_tags
- field_dependence_tags
- root_origin_ids

At minimum the starter slice should distinguish continuation outcomes:

- `continue_to_governed_act`
- `await_authority`
- `emit_governed_communication`
- `pause_blocked`
- `stop_complete`
- `escalate_for_review`

Only `continue_to_governed_act` may descend into the shipped governed act ladder in
`V60-A`.

If `continue_to_governed_act` is selected, the selected-next-path field should remain
closed to the exact already shipped downstream `V59` continuity-bound exemplar only.

`emit_governed_communication` should remain explicit in the starter outcome family,
but only as a continuation posture. It must not be over-read as governed
communication-packet authorization.

## Defer To Later Slice Or Family

- governed communication ingress / egress packets
- office binding and rewitness gate law
- residual refresh over multiple reintegrations
- structured reproposal / escalation queue surfaces
- connector admission and external assistant bridge
- remote operator control surfaces
- repo-bound writable-surface authority
- delegated export / worker reconciliation

## Do Not Import

- raw transcript semantics as starter seed intent
- generic chat memory as loop-state identity
- connector traffic as seed-intent law
- `TaskResidual` as ongoing permission
- prior ticket or prior reintegration as standing authority
- communication packet law or office binding in `V60-A`
- ticket-duration widening
