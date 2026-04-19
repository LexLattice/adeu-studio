# Draft ADEU Repo-Bound Writable-Surface Authority V64B Implementation Mapping v0

Status: support note for the `V64-B` implementation pass after `V64-A` starter
closure on `main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a bounded
`V64-B` slice should add one writable-surface restoration / reintegration seam
over the already shipped `V64-A` writable-surface descriptor / lease / admission
lineage without mutating repo-surface selection law, widening write semantics, or
minting broad repo authority by default.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v49.md`
- `docs/ARCHITECTURE_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_FAMILY_v0.md`
- `docs/DRAFT_ADEU_REPO_BOUND_WRITABLE_SURFACE_AUTHORITY_V64_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS176.md`

## Carry Forward Nearly As-Is

- the shipped `V64-A` writable-surface descriptor
- the shipped `V64-A` repo write lease
- the shipped `V64-A` repo write surface admission record
- the shipped exact write-effect observation / conformance / admission lineage
  over the `V64-A` target
- shipped `V59-A`, `V59-B`, and `V59-C` continuity-region / occupancy /
  reintegration posture as consumed basis only
- shipped `V60-A`, `V60-B`, and `V60-C` continuation / refresh / advisory
  posture as consumed basis only
- shipped `V61-A`, `V61-B`, and `V61-C` communication / bridge-office /
  rewitness / advisory posture as consumed basis only
- shipped `V62-A`, `V62-B`, and `V62-C` connector posture as separate sibling law
  only
- shipped `V63-A`, `V63-B`, and `V63-C` remote-operator posture as separate
  sibling law only
- the rule that writable-surface entitlement is not shell / execute / dispatch /
  delegated-worker authority
- the rule that mutation-semantics widening remains deferred past `V64-B`

## Re-Author With Repo Alignment

Candidate new restoration surfaces:

- `agentic_de_repo_write_restoration_record@1`
- `agentic_de_repo_write_reintegration_report@1`

Those surfaces should remain bounded to the already shipped `V64-A` writable
surface only.

They should decide only:

- whether one exact admitted in-surface target can be restored over the same
  shipped descriptor / lease / admission lineage; and
- whether one reintegration report can remain replayable and fail closed over that
  same restoration lineage.

They should keep:

- no fresh writable-surface selection
- no fresh lease issuance
- no all-repo authority
- no append / overwrite / rename / delete widening
- no shell or terminal control
- no execute widening
- no dispatch widening
- no delegated worker export or reconciliation
- no remote-operator law mutation
- no connector-law mutation

`V64-B` should keep explicit:

- the selected writable surface remains the shipped `V64-A` surface only
- the selected target remains the shipped exact admitted target only
- restoration consumes shipped descriptor / lease / admission basis rather than
  minting new writable entitlement
- restoration consumes shipped concrete write-effect lineage rather than
  pretending writable-surface entitlement alone is what gets restored
- reintegration consumes shipped restoration basis rather than reopening surface
  selection
- target membership basis and target occupancy/admissibility basis remain
  explicit:
  - same in-surface target-membership law only
  - same admitted target occupancy/admissibility carry-through only
- continuity lineage may contextualize restoration posture, but is not fresh
  writable entitlement
- communication lineage may contextualize restoration posture, but is not the
  lease or restoration authority by itself
- connector and remote sibling posture remain contextual only here
- mutation semantics remain preserved from `V64-A`:
  - same narrow `local_write` / `create_new` posture only
  - no broader mutation semantics yet
- restoration and reintegration remain typed and replayable:
  - same shipped `V64-A` basis
  - same consumed shipped `V59` / `V60` / `V61` basis
  - same frozen policy anchor
  - same restoration / reintegration output
- missing or inconsistent basis fails closed
- restoration is not fresh target admission by itself
- one selected writable-surface restoration path may not generalize by default
  into:
  - all-repo authority
  - shell authority
  - execute authority
  - dispatch authority
  - delegated worker authority
  - connector law
  - remote-operator law

## Do Not Import

- fresh writable-surface selection law
- fresh lease issuance law
- broader per-surface target authority
- fresh target admission law
- broader write-mutation semantics
- all-repo writable authority
- shell or terminal control
- execute widening
- dispatch widening
- delegated worker export / reconciliation
- remote control law
- connector law
