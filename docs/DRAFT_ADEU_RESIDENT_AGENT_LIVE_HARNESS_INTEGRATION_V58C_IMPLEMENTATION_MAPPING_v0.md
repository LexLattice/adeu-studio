# Draft ADEU Resident-Agent Live Harness Integration V58C Implementation Mapping v0

Status: support note for the `V58-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later `V58-C`
slice should evaluate the live harness-bound path for replay / drift hardening without
mutating live behavior by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v41.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- `V58-A` live-turn admission / handoff / reintegration
- `V58-B` explicit restoration-state integration if that slice lands
- shipped `V57-C` path-level hardening advice as advisory shaping input only

## Re-Author With Repo Alignment

Candidate new surface:

- `agentic_de_live_harness_hardening_register@1`

That surface should remain advisory-only in this slice.

It should decide only whether the exact live harness-bound starter path deserves later
hardening or broader replay checks, while keeping:

- no live behavior mutation by default
- no ticket-law mutation
- no checkpoint-law mutation
- no class widening
- no dispatch
- no product/UI rollout

`V58-C` should keep explicit:

- the selected hardening target is the shipped live harness-bound observed-and-restored
  `create_new` exemplar only
- reuse of the shipped `V58-A` admission / handoff / reintegration surfaces does not
  imply broader live-turn law selection
- reuse of the shipped `V58-B` restoration-state surfaces does not imply broader
  restoration-family or replay-family selection
- committed lane artifacts outrank narrative docs when the hardening register is
  derived
- the register depends on the shipped boundedness / reintegration verdicts, not on
  artifact refs alone
- the recommendation function must remain extensional and replayable:
  - same selected evidence chain
  - same frozen policy
  - same recommendation outcome
- evidence basis remains distinct from recommendation outcome
- common lineage roots remain non-independent at the advisory layer:
  - observation, conformance, turn reintegration, and restoration reintegration from
    the same bounded exemplar lineage may support traceability
  - they may not count as independent escalation support by repetition alone
- the selected exemplar may not generalize by default into:
  - class-level `local_write` conclusions
  - restoration-family conclusions
  - replay-family conclusions
- `candidate_for_later_harness_hardening` may nominate only a later bounded
  evaluation target; it does not define the scope of later hardening unless a later
  lock selects that scope explicitly
- the surface remains path-level advisory only:
  - not a family migration surface
  - not a live entitlement surface

Recommended decision vocabulary:

- allowed:
  - `keep_warning_only`
    - retain the current advisory posture over the exact path
    - no present candidate nomination
  - `needs_more_evidence`
    - record current evidentiary insufficiency only
    - not a soft escalation or deferred entitlement by itself
  - `candidate_for_later_harness_hardening`
    - nominate one later bounded evaluation target only
    - do not define later hardening scope without a later lock
  - `not_selected_for_escalation`
    - record negative selection on the current evidence basis
- forbidden:
  - `gate_now`
  - `ticket_now`
  - `replay_widen_now`
  - `dispatch_now`
  - `ci_required_now`

## Do Not Import

- advisory-to-live promotion
- generic harness sovereignty
- exemplar-to-class generalization
