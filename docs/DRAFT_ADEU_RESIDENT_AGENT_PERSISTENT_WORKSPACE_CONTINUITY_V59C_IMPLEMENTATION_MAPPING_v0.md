# Draft ADEU Resident-Agent Persistent Workspace Continuity V59C Implementation Mapping v0

Status: support note for the `V59-C` implementation pass after `V59-B` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later `V59-C`
slice should evaluate the continuity-bound path for hardening / drift without mutating
live behavior by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v42.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_V59_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_V59B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- `V59-A` continuity region / admission / occupancy / reintegration
- `V59-B` explicit continuity-safe restoration
- shipped `V57-C` and `V58-C` advisory hardening posture as shaping input only

## Re-Author With Repo Alignment

Candidate new surface:

- `agentic_de_workspace_continuity_hardening_register@1`

That surface should remain advisory-only in this slice.

It should decide only whether the exact continuity-bound starter path deserves later
hardening or broader drift checks, while keeping:

- no live behavior mutation by default
- no checkpoint-law mutation
- no ticket-law mutation
- no continuity-entitlement widening
- no replay widening
- no execute widening
- no dispatch

`V59-C` should keep explicit:

- the selected hardening target is the shipped continuity-bound observed-and-restored
  `create_new` exemplar only
- reuse of the shipped `V59-A` continuity surfaces does not imply broader
  continuity-family selection
- reuse of the shipped `V59-B` continuity-safe restoration surfaces does not imply
  broader restoration-family or replay-family selection
- committed lane artifacts outrank narrative docs when the hardening register is
  derived
- the hardening register carries one explicit frozen-policy anchor:
  - same selected evidence basis
  - same frozen policy anchor
  - same recommendation outcome
- the register depends on the shipped occupancy / boundedness / reintegration verdicts,
  not on artifact refs alone
- the register carries forward the shipped `V59-B` restoration freshness and baseline
  verdicts explicitly:
  - restoration-time continuation verdict
  - prior governed-state baseline-match verdict
  - bounded compensating-scope-match verdict
- the recommendation function must remain extensional and replayable:
  - same selected evidence basis
  - same frozen policy anchor
  - same recommendation outcome
- evidence basis remains distinct from recommendation outcome
- common lineage roots remain non-independent at the advisory layer
- the selected exemplar may not generalize by default into:
  - class-level `local_write` conclusions
  - continuity-family conclusions
  - restoration-family conclusions
  - replay-family conclusions
- `candidate_for_later_continuity_hardening` may nominate only one later bounded
  evaluation target; it does not define the scope of later hardening unless a later
  lock selects that scope explicitly
- the surface remains path-level advisory only:
  - not a family migration surface
  - not a live entitlement surface

Recommended decision vocabulary:

- allowed:
  - `keep_warning_only`
  - `needs_more_evidence`
  - `candidate_for_later_continuity_hardening`
  - `not_selected_for_escalation`
- forbidden:
  - `gate_now`
  - `ticket_now`
  - `resume_now`
  - `dispatch_now`
  - `ci_required_now`

## Do Not Import

- advisory-to-live promotion
- generic workspace sovereignty
- exemplar-to-class generalization
- continuity-as-replay-law by implication alone
