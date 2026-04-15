# Draft ADEU Resident-Agent Continuation And Residual-Intent V60B Implementation Mapping v0

Status: support note for the `V60-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the second
`V60` slice should refresh one already established `V60-A` continuation lineage after
one latest reintegrated governed act, producing one refreshed residual packet and one
refreshed continuation decision without reopening starter seed ingress, widening
ticket duration, or silently minting `V61` communication law.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_EXTERNALIZED_REASONING_KERNEL_v0.md`
- `docs/DRAFT_WCPGC_CORE_AND_STRICT_V0_v0.md`

## Carry Forward Nearly As-Is

- shipped `V60-A` seed-intent / charter / residual / loop-state / continuation-decision
  semantics
- shipped `V56` packet / proposal / checkpoint / ticket semantics
- shipped `V57` observation / restoration / hardening semantics
- shipped `V58` live admission / handoff / reintegration semantics
- shipped `V59` continuity / continuity-safe restoration / advisory continuity-hardening
  semantics
- the rule that `V56` ticket duration stays `single_step_local`
- the rule that transcript, chat memory, and prior continuity success remain context at
  most, never standing authority
- the rule that `emit_governed_communication` remains posture-only until `V61`

## Re-Author With Repo Alignment

`V60-B` should add exactly:

- `agentic_de_task_residual_refresh_packet@1`
- `agentic_de_continuation_refresh_decision_record@1`

`V60-B` should consume:

- one shipped `agentic_de_seed_intent_record@1`
- one shipped `agentic_de_task_charter_packet@1`
- one shipped `agentic_de_task_residual_packet@1`
- one shipped `agentic_de_loop_state_ledger@1`
- one shipped `agentic_de_continuation_decision_record@1`
- one latest reintegrated downstream governed act lineage over the same exact shipped
  `V59` continuity-bound exemplar
- one explicit `agentic_de_lane_drift_record@1`
- committed closeout evidence from shipped earlier lanes as drift guard only

Those prior artifacts should outrank narrative interpretation for drift checking, but
they should not become fresh continuation authority by mere existence.

The shipped `agentic_de_loop_state_ledger@1` remains the canonical stable loop
identity anchor in `V60-B`.

- `V60-B` refresh surfaces advance frontier over that same loop identity
- no loop-state refresh or replacement artifact is selected here
- prior ledger reuse is identity anchoring only, not standing permission

## Refresh Law

The second continuation slice should make these laws explicit:

- refresh is downstream of one already established `V60-A` loop identity
- the shipped `V60-A` loop-state ledger remains the canonical loop anchor in this
  slice
- refresh is not new starter ingress
- refresh must remain typed and replayable:
  - same shipped loop identity
  - same selected prior continuation lineage
  - same selected latest reintegrated act identity
  - same frozen policy basis
  - same refreshed residual and same refreshed continuation posture
- refresh remains derived:
  - not human-authored law
  - not standing authority
  - not stretched ticket authority
- only one latest reintegrated act lineage is admitted in `V60-B`
- latest reintegrated act selection must be explicit and fail-closed:
  - one latest reintegrated act identity only
  - one explicit selection basis only
  - ambiguity blocks refresh rather than being summarized away
- block / rejection / reproposal posture must remain typed
- `reproposal_required` is a continuation posture only:
  - it records that the current charter / residual frontier may not lawfully
    continue as-is
  - later structured ingress or governed communication is needed to proceed
  - it is not implicit charter amendment
  - it does not mint new seed ingress law by itself
  - it does not reopen raw transcript semantics
- `emit_governed_communication` remains posture-only:
  - no `V61` packet law here
- any future act still requires fresh-step `V58` / `V56` governance

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

`agentic_de_task_residual_refresh_packet@1` should at minimum externalize:

- prior_task_charter_ref
- prior_task_residual_ref
- prior_loop_state_ledger_ref
- prior_loop_identity_ref
- prior_continuation_decision_ref
- latest_reintegrated_act_identity
- latest_reintegrated_act_selection_basis_summary
- latest_live_turn_reintegration_ref
- latest_continuity_reintegration_ref
- latest_continuity_restoration_reintegration_ref_or_none
- refreshed_frontier_summary
- refreshed_open_obligation_summary
- refreshed_blocker_summary
- refreshed_open_approval_refs
- refreshed_owed_communication_posture_summary
- residual_refresh_basis_summary
- field_origin_tags
- field_dependence_tags
- root_origin_ids

`agentic_de_continuation_refresh_decision_record@1` should at minimum externalize:

- prior_loop_state_ledger_ref
- stable_loop_identity_ref
- refreshed_task_residual_ref
- latest_reintegrated_act_identity
- refresh_outcome
- refresh_reason_codes
- frozen_policy_anchor_ref
- evidence_basis_summary
- selected_next_path_summary_or_none
- reproposal_basis_summary_or_none
- field_origin_tags
- field_dependence_tags
- root_origin_ids

At minimum the slice should distinguish refresh outcomes:

- `continue_to_governed_act`
- `await_authority`
- `emit_governed_communication`
- `pause_blocked`
- `stop_complete`
- `reproposal_required`
- `escalate_for_review`

Only `continue_to_governed_act` may descend into the shipped governed act ladder in
`V60-B`.

If `continue_to_governed_act` is selected, the selected-next-path field should remain
closed to the exact already shipped downstream `V59` continuity-bound exemplar only.

If `reproposal_required` is selected, the slice should emit only typed reproposal
posture and basis. It must mean the current charter / residual frontier may not
lawfully continue as-is and that later structured ingress or governed communication
is needed. It must not mint new starter ingress law, implicit charter amendment, or
raw message ingress.

## Defer To Later Slice Or Family

- governed communication ingress / egress packets
- office binding and rewitness gate law
- multiple-refresh chains across many reintegrations
- new starter seed ingress compilation
- connector admission and external assistant bridge
- remote operator control surfaces
- repo-bound writable-surface authority
- delegated export / worker reconciliation
- advisory continuation hardening / migration

## Do Not Import

- raw transcript semantics as refreshed reproposal input
- generic chat memory as continuation authority
- prior successful continuation decision as standing permission
- prior ticket or prior reintegration as standing authority
- communication packet law or office binding in `V60-B`
- ticket-duration widening
