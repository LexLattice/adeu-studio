# Draft ADEU Resident-Agent Continuation And Residual-Intent V60C Implementation Mapping v0

Status: support note for the `V60-C` implementation pass after `V60-B` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later
`V60-C` slice should evaluate the shipped continuation lineage for advisory
hardening / migration without mutating live behavior by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v43.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONTINUATION_AND_RESIDUAL_INTENT_V60B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V60-A` seed-intent / charter / residual / loop-state / continuation
  decision lineage
- shipped `V60-B` residual refresh / continuation refresh lineage
- shipped `V57-C`, `V58-C`, and `V59-C` advisory hardening posture as shaping input
  only

## Re-Author With Repo Alignment

Candidate new surface:

- `agentic_de_continuation_hardening_register@1`

That surface should remain advisory-only in this slice.

It should decide only whether the exact shipped continuation lineage deserves later
hardening or later bounded migration evaluation, while keeping:

- no live behavior mutation by default
- no checkpoint-law mutation
- no ticket-law mutation
- no task-charter mutation
- no residual-refresh mutation
- no continuity admission / reintegration / restoration mutation
- no repo-authority widening
- no replay / resume widening
- no execute widening
- no dispatch widening
- no communication packet law or office binding

`V60-C` should keep explicit:

- the selected hardening target is the shipped exact `V60-A` / `V60-B`
  continuation lineage over the continuity-bound `local_write/create_new` exemplar
  only
- reuse of the shipped `V60-A` starter surfaces does not imply broader starter
  ingress, broader charter law, or broader continuation-family selection
- reuse of the shipped `V60-B` refresh surfaces does not imply broader reproposal
  law, broader escalation law, or multi-step ticket duration
- committed lane artifacts outrank narrative docs when the hardening register is
  derived
- the hardening register carries one explicit frozen-policy anchor:
  - same selected evidence basis
  - same frozen policy anchor
  - same recommendation outcome
- the recommendation function remains extensional and replayable:
  - same shipped loop identity
  - same latest reintegrated act identity
  - same refresh outcome
  - same frozen policy anchor
  - same recommendation outcome
- evidence basis remains distinct from recommendation outcome
- common lineage roots remain non-independent at the advisory layer
- the register should expose provenance and non-independence directly, not only by
  implication:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`
- the register depends on the shipped continuation verdicts, not on artifact refs
  alone:
  - starter continuation outcome
  - latest-act selection basis
  - refresh outcome
  - selected-next-path posture or reproposal posture
- `reproposal_required` remains posture-only at the advisory layer:
  - it is not implicit charter amendment
  - it is not new seed ingress
  - it is not communication packet law
- `emit_governed_communication` remains posture-only at the advisory layer:
  - it is not `V61` packet law
  - it is not office binding
  - it is not raw transcript or connector ingress law
- the selected exemplar may not generalize by default into:
  - class-level continuation law
  - family-level continuation law
  - family-level migration law
  - communication-family law
  - repo-authority law
  - replay / resume law
  - broader autonomy claims
- `needs_more_evidence` remains non-entitling and non-escalating by itself
- `candidate_for_later_continuation_hardening` remains non-entitling and
  non-escalating by itself
- `candidate_for_later_continuation_hardening` may nominate only one later bounded
  evaluation target; it does not define later scope unless a later lock selects it
  explicitly
- `candidate_for_later_continuation_migration` remains non-entitling and
  non-escalating by itself:
  - later migration scope remains unspecified unless a later lock selects it
    explicitly
- `not_selected_for_escalation` records negative selection on the current evidence:
  - it is not a soft backlog signal
- the surface remains path-level advisory only:
  - not a family migration surface
  - not a live entitlement surface

Recommended decision vocabulary:

- allowed:
  - `keep_warning_only`
  - `needs_more_evidence`
  - `candidate_for_later_continuation_hardening`
  - `candidate_for_later_continuation_migration`
  - `not_selected_for_escalation`
- forbidden:
  - `gate_now`
  - `ticket_now`
  - `resume_now`
  - `dispatch_now`
  - `communicate_now`

## Do Not Import

- advisory-to-live promotion
- raw transcript or generic chat memory as advisory authority basis
- reproposal posture as new ingress law
- continuation hardening as implicit communication law
- exemplar-to-family generalization
- continuation lineage as standing permission
