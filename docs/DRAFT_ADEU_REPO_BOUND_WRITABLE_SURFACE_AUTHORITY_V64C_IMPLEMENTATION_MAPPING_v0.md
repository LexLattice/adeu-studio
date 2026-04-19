# Draft ADEU Repo-Bound Writable-Surface Authority V64C Implementation Mapping v0

Status: support note for the `V64-C` implementation pass after `V64-B` closure
on `main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a bounded
`V64-C` slice should evaluate the shipped writable-surface lineage for advisory
hardening / provenance drift without mutating live repo-write behavior by
default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v49.md`
- `docs/ARCHITECTURE_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_V64_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_V64B_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V64-A` writable-surface descriptor / lease / admission lineage
- shipped `V64-B` repo-write restoration / reintegration lineage
- shipped exact admitted target posture over the selected writable surface
- shipped exact concrete write-effect lineage over that admitted target
- shipped `V59-A`, `V59-B`, and `V59-C` continuity posture as consumed basis only
- shipped `V60-A`, `V60-B`, and `V60-C` continuation posture as consumed basis only
- shipped `V61-A`, `V61-B`, and `V61-C` communication posture as consumed basis
  only
- shipped `V62-A`, `V62-B`, and `V62-C` connector posture as separate sibling law
  only
- shipped `V63-A`, `V63-B`, and `V63-C` remote-operator posture as separate
  sibling law only
- the rule that writable-surface entitlement is not shell / execute / dispatch /
  delegated-worker authority
- the rule that restoration and reintegration are not fresh entitlement by
  themselves

## Re-Author With Repo Alignment

Candidate new surface:

- `agentic_de_repo_writable_surface_hardening_register@1`

That surface should remain advisory-only in this slice.

It should decide only whether the exact shipped `V64-A` / `V64-B` writable-surface
lineage deserves later hardening or later bounded writable-surface migration
evaluation, while keeping:

- no fresh writable-surface selection
- no fresh lease issuance
- no fresh target admission
- no live restoration or reintegration mutation
- no communication mutation
- no continuation mutation
- no connector-law mutation
- no remote-operator-law mutation
- no broad repo-admin law
- no all-repo authority
- no shell authority
- no execute widening
- no dispatch widening
- no delegated worker export or reconciliation
- no advisory-to-live promotion

`V64-C` should keep explicit:

- the selected hardening target is the shipped exact `V64-A` / `V64-B`
  writable-surface lineage only:
  - one shipped writable-surface descriptor only
  - one shipped repo write lease only
  - one shipped repo write surface admission only
  - one shipped exact admitted target only
  - one shipped restoration / reintegration lineage where relevant
- committed lane artifacts outrank narrative docs when the hardening register is
  derived
- the hardening register carries one explicit frozen-policy anchor:
  - same selected evidence basis
  - same frozen policy anchor
  - same recommendation outcome
- the recommendation function remains extensional and replayable:
  - same writable-surface basis
  - same selected target posture
  - same restoration / reintegration basis where selected
  - same consumed shipped `V59` / `V60` / `V61` basis
  - same frozen policy anchor
  - same recommendation outcome
- evidence basis remains distinct from recommendation outcome
- common lineage roots remain non-independent at the advisory layer
- the register should expose provenance and non-independence directly, not only
  by implication:
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`
- the register depends on shipped writable verdicts and posture, not on refs alone:
  - selected writable-surface identity
  - lease verdict
  - target admission verdict
  - selected target path summary
  - selected concrete write-effect posture where consumed
  - selected restoration / reintegration status summary where present
  - preserved write-semantics summary
  - latest continuation basis
  - latest continuation basis selection summary
  - selected governed communication posture where consumed
- optional upstream restoration / reintegration basis remains fail-closed:
  - if both optional restoration and reintegration refs are `none`, the
    hardening register may not overread restoration-local evidence
  - restoration ref may appear without reintegration ref when only shipped
    restoration-local evidence is selected
  - reintegration ref may not appear without restoration ref
  - restoration and reintegration refs may co-appear only when they remain the
    same shipped restoration chain
  - if one is present, it must remain consistent with the selected writable
    surface, admitted target, and preserved write posture
  - inconsistent optional restoration / reintegration carry-through fails closed
- the selected writable exemplar may not generalize by default into:
  - all-repo authority
  - broad repo-admin law
  - shell authority
  - execute authority
  - dispatch authority
  - delegated-worker authority
  - connector law
  - remote-operator law
  - all-device or all-surface law
- `needs_more_evidence` remains non-entitling and non-escalating by itself
- `keep_warning_only` retains current advisory posture only
- `candidate_for_later_writable_surface_hardening` remains non-entitling and
  non-escalating by itself:
  - later hardening scope remains unspecified unless a later lock selects it
    explicitly
- `candidate_for_later_writable_surface_migration` remains non-entitling and
  non-escalating by itself:
  - later migration scope remains unspecified unless a later lock selects it
    explicitly
- `not_selected_for_escalation` records negative selection on the current
  evidence:
  - it is not a soft backlog signal
- the surface remains path-level advisory only:
  - not a live entitlement surface
  - not a mutation surface

Recommended decision vocabulary:

- allowed:
  - `keep_warning_only`
  - `needs_more_evidence`
  - `candidate_for_later_writable_surface_hardening`
  - `candidate_for_later_writable_surface_migration`
  - `not_selected_for_escalation`
- forbidden:
  - `select_surface_now`
  - `lease_now`
  - `admit_target_now`
  - `restore_now`
  - `repo_write_now`
  - `execute_now`
  - `dispatch_now`

## Do Not Import

- advisory-to-live promotion
- prior successful write or restoration as authority basis by itself
- reintegration posture as authority basis by itself
- exemplar-to-family or exemplar-to-repo generalization
- connector law
- remote-operator law
- execute widening
- dispatch widening
- delegated worker widening
