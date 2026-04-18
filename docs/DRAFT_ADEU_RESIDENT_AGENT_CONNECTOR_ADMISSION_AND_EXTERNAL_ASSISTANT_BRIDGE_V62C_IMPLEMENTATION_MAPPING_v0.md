# Draft ADEU Resident-Agent Connector Admission And External Assistant Bridge V62C Implementation Mapping v0

Status: support note for the `V62-C` implementation pass after `V62-B` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a later
`V62-C` slice should evaluate the shipped connector admission and external-assistant
bridge lineage for advisory connector hardening / provenance drift without mutating
live behavior by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v45.md`
- `docs/ARCHITECTURE_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_CONNECTOR_ADMISSION_AND_EXTERNAL_ASSISTANT_BRIDGE_V62B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V62-A` connector admission and external-assistant ingress bridge lineage
- shipped `V62-B` external-assistant egress bridge lineage
- shipped `V61-A`, `V61-B`, and `V61-C` communication / bridge-office /
  rewitness / advisory hardening lineage as consumed basis only
- shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory posture
  as shaping input only
- the rule that connector transport is transport only, not authority
- the rule that external-assistant ingress/egress payload remains bridge material,
  not native witness, task-law ingress, continuation mutation, bridge office, repo
  authority, or execute authority
- the rule that human-via-connector remains unselected in this family slice

## Re-Author With Repo Alignment

Candidate new surface:

- `agentic_de_connector_bridge_hardening_register@1`

That surface should remain advisory-only in this slice.

It should decide only whether the exact shipped `V62-A` / `V62-B` connector
lineage deserves later connector hardening or later bounded connector migration
review, while keeping:

- no connector admission mutation
- no ingress-bridge mutation
- no egress-bridge mutation
- no bridge-office mutation
- no rewitness mutation
- no communication mutation
- no continuation mutation
- no human-via-connector selection
- no broader connector-fleet admission
- no remote-operator law
- no repo-authority widening
- no execute widening
- no dispatch widening

`V62-C` should keep explicit:

- the selected hardening target is the shipped exact `V62-A` / `V62-B` admitted
  connector lineage over the continuity-bound `local_write/create_new` exemplar
  only
- committed lane artifacts outrank narrative docs when the hardening register is
  derived
- the hardening register carries one explicit frozen-policy anchor:
  - same selected evidence basis
  - same frozen policy anchor
  - same recommendation outcome
- explicit frozen-policy anchor remains required for replayability
- the recommendation function remains extensional and replayable:
  - same connector admission lineage
  - same ingress and egress bridge lineage
  - same bridge-office / rewitness posture where selected
  - same communication hardening posture where consumed
  - same frozen policy anchor
  - same recommendation outcome
- evidence basis remains distinct from recommendation outcome
- common lineage roots remain non-independent at the advisory layer
- the register should expose provenance and non-independence directly, not only by
  implication:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`
- the register depends on shipped connector and communication verdicts, not on refs
  alone:
  - selected connector provider
  - selected connector principal
  - admission verdict
  - selected bridge-office posture where selected
  - selected rewitness outcome where selected
  - positive rewitness basis / certificate posture where present
  - latest continuation basis
  - latest continuation basis selection summary
  - selected communication hardening outcome where consumed
- positive rewitness basis consistency remains fail-closed:
  - if no positive rewitness was selected upstream, positive rewitness basis and
    certificate posture remain `none`
  - if positive rewitness basis or certificate posture is carried, it must match
    the selected upstream rewitness posture
  - inconsistent positive rewitness carry-through fails closed
- the selected connector exemplar may not generalize by default into:
  - broader connector-fleet trust law
  - human-via-connector law
  - remote-operator law
  - bridge-office-family law
  - rewitness-family law
  - repo-authority law
  - execute-authority law
- `needs_more_evidence` remains non-entitling and non-escalating by itself
- `keep_warning_only` retains current advisory posture only
- `candidate_for_later_connector_hardening` remains non-entitling and
  non-escalating by itself:
  - later connector-hardening scope remains unspecified unless a later lock selects
    it explicitly
- `candidate_for_later_connector_migration` remains non-entitling and
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
  - `candidate_for_later_connector_hardening`
  - `candidate_for_later_connector_migration`
  - `not_selected_for_escalation`
- forbidden:
  - `admit_now`
  - `bridge_now`
  - `human_via_connector_now`
  - `execute_now`
  - `dispatch_now`

## Do Not Import

- advisory-to-live promotion
- connector transport as advisory authority basis
- external-assistant payload as native witness
- bridge-office or rewitness posture as connector admission law
- exemplar-to-fleet or exemplar-to-principal generalization
- human-via-connector law
- remote-operator law
- repo-bound writable-surface widening
- execute widening
- dispatch widening
