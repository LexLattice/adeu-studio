# Draft ADEU Repo-Bound Writable-Surface Authority V64A Implementation Mapping v0

Status: support note for the `V64-A` implementation pass after `V63` closed on
`main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the starter
`V64-A` slice should widen from one exact shipped write exemplar into one selected
subtree or file-set writable surface while preserving the currently selected narrow
write semantics and without mutating remote, connector, execute, or delegated-worker
law by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v49.md`
- `docs/ARCHITECTURE_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_V64_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/v60+ plan gptpro.md`

## Carry Forward Nearly As-Is

- shipped `V59-A`, `V59-B`, and `V59-C` continuity-region / occupancy / restoration
  / hardening posture
- shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory posture
- shipped `V61-A`, `V61-B`, and `V61-C` communication / bridge-office /
  rewitness / advisory hardening lineage as consumed basis only
- shipped `V62-A`, `V62-B`, and `V62-C` connector posture as separate sibling law
  only
- shipped `V63-A`, `V63-B`, and `V63-C` remote operator posture as separate
  sibling law only
- the rule that continuity region is not writable entitlement
- the rule that communication lineage may contextualize but not mint repo authority
- the rule that remote operator law remains outside `V64`

## Re-Author With Repo Alignment

Candidate new starter surfaces:

- `agentic_de_repo_writable_surface_descriptor@1`
- `agentic_de_repo_write_lease_record@1`
- `agentic_de_repo_write_surface_admission_record@1`

Those surfaces should remain bounded to one declared writable surface only.

They should decide only:

- whether one selected subtree or file-set is the writable work surface here;
- whether one bounded write lease is lawful over that selected writable surface; and
- whether one in-surface target is admissible under that same lease while
  preserving the currently selected narrow local-write semantics.

They should keep:

- no all-repo authority
- no append / overwrite / rename / delete widening
- no shell or terminal control
- no execute widening
- no dispatch widening
- no delegated worker export or reconciliation
- no remote-operator law mutation
- no connector-law mutation

`V64-A` should keep explicit:

- the selected writable surface is one declared subtree or file-set only
- writable-surface membership is canonical, normalized, and fail-closed
- inclusion / exclusion basis is explicit
- continuity region remains persistence/context law only
- writable-surface descriptor and lease remain entitlement law only
- communication lineage may contextualize or justify write posture, but is not
  itself the lease or repo-surface authority
- connector and remote sibling posture may constrain context at most, but are not
  consumed writable entitlement basis in `V64-A`
- starter widening is surface-only:
  - preserve current `local_write`
  - preserve current `create_new`
  - no broader mutation semantics yet
- per-target occupancy/admissibility remains explicit:
  - the lease alone is not blanket entitlement for every path in the selected
    surface
  - exact target admissibility basis remains required
- typed lease verdict family remains explicit and bounded:
  - `admitted`
  - `rejected_surface_not_selected`
  - `rejected_target_not_in_surface`
  - `rejected_missing_basis`
  - `rejected_inconsistent_basis`
- typed admission verdict family remains explicit and bounded:
  - `admitted`
  - `rejected_target_not_in_surface`
  - `rejected_target_not_admissible`
  - `rejected_missing_basis`
  - `rejected_inconsistent_basis`
- the descriptor / lease / admission surfaces remain typed and replayable:
  - same selected surface basis
  - same consumed shipped `V59` / `V60` / `V61` basis
  - same frozen policy anchor
  - same descriptor / lease / admission output
- one selected writable surface may not generalize by default into:
  - all-repo authority
  - shell authority
  - execute authority
  - dispatch authority
  - delegated worker authority
  - remote operator law

## Do Not Import

- all-repo writable authority
- broader write-mutation semantics
- shell or terminal control
- execute widening
- dispatch widening
- delegated worker export / reconciliation
- remote control law
- connector law
