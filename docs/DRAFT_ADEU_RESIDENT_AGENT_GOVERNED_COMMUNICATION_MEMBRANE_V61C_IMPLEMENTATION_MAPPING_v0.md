# Draft ADEU Resident-Agent Governed Communication Membrane V61C Implementation Mapping v0

Status: support note for the `V61-C` implementation pass after `V61-B` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later
`V61-C` slice should evaluate the shipped governed communication lineage for
advisory hardening / migration without mutating live behavior by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v44.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_V61_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_GOVERNED_COMMUNICATION_MEMBRANE_V61B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V61-A` communication ingress / descriptor / interpretation / egress
  lineage
- shipped `V61-B` bridge-office binding and rewitness gate lineage
- shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory posture as
  shaping input only
- the rule that communication access is not bridge office
- the rule that positive rewitness remains witness-candidate posture only in `V61-B`
- the rule that transcript and generic chat memory remain observability surfaces, not
  native witness

## Re-Author With Repo Alignment

Candidate new surface:

- `agentic_de_governed_communication_hardening_register@1`

That surface should remain advisory-only in this slice.

It should decide only whether the exact shipped `V61-A` / `V61-B` governed
communication lineage deserves later communication hardening or later bounded
bridge-office / rewitness migration evaluation, while keeping:

- no live behavior mutation by default
- no communication ingress / egress mutation
- no bridge-office binding mutation
- no rewitness mutation
- no task-charter mutation
- no residual mutation
- no loop-state mutation
- no continuation mutation
- no connector transport law
- no remote-operator law
- no repo-authority widening
- no execute widening
- no dispatch widening

`V61-C` should keep explicit:

- the selected hardening target is the shipped exact `V61-A` / `V61-B`
  communication lineage over the continuity-bound `local_write/create_new` exemplar
  only
- reuse of the shipped `V61-A` starter surfaces does not imply broader communication
  ingress law, broader communication-family law, or broader surface-family
  selection
- reuse of the shipped `V61-B` bridge-office and rewitness surfaces does not imply
  native witness law, reintegration closure, act authority, or repo-write authority
- committed lane artifacts outrank narrative docs when the hardening register is
  derived
- the hardening register carries one explicit frozen-policy anchor:
  - same selected evidence basis
  - same frozen policy anchor
  - same recommendation outcome
- the recommendation function remains extensional and replayable:
  - same communication lineage
  - same bridge-office posture
  - same rewitness outcome
  - same frozen policy anchor
  - same recommendation outcome
- evidence basis remains distinct from recommendation outcome
- common lineage roots remain non-independent at the advisory layer
- the register should expose provenance and non-independence directly, not only by
  implication:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`
- the register depends on shipped communication verdicts, not on artifact refs alone:
  - selected surface facts
  - selected bridge-office posture
  - selected rewitness outcome
  - explicit positive rewitness basis when present:
    - `witness_basis_ref_or_none`
    - `certificate_ref_or_none`
  - latest continuation basis
  - latest continuation basis selection summary
- positive rewitness remains posture-only at the advisory layer:
  - it is not native witness
  - it is not reintegration closure
  - it is not act authority
  - it is not repo-write authority
- the selected exemplar may not generalize by default into:
  - connector-family law
  - remote-operator law
  - bridge-office-family law
  - rewitness-family law
  - independent law for other communication surfaces beyond the same backend seam
  - repo-authority law
  - execute-authority law
  - broader autonomy claims
- `needs_more_evidence` remains non-entitling and non-escalating by itself
- `candidate_for_later_communication_hardening` remains non-entitling and
  non-escalating by itself:
  - later communication-hardening scope remains unspecified unless a later lock
    selects it explicitly
- `candidate_for_later_bridge_office_or_rewitness_migration` remains non-entitling
  and non-escalating by itself:
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
  - `candidate_for_later_communication_hardening`
  - `candidate_for_later_bridge_office_or_rewitness_migration`
  - `not_selected_for_escalation`
- forbidden:
  - `gate_now`
  - `bridge_now`
  - `rewitness_now`
  - `transport_now`
  - `dispatch_now`

## Do Not Import

- advisory-to-live promotion
- raw transcript or generic chat memory as advisory authority basis
- bridge-office posture as native witness law
- rewitness posture as native witness law
- communication hardening as implicit connector law
- exemplar-to-family generalization
- governed communication lineage as standing permission
