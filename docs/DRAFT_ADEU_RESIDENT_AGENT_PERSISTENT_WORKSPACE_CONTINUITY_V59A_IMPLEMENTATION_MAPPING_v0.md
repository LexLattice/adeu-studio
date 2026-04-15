# Draft ADEU Resident-Agent Persistent Workspace Continuity V59A Implementation Mapping v0

Status: support note for the `V59-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the first `V59`
slice should bind one already governed live turn to one declared persistent continuity
region without letting carried-forward workspace state become ambient authority.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v42.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_PERSISTENT_WORKSPACE_CONTINUITY_V59_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_RESIDENT_AGENT_LIVE_HARNESS_INTEGRATION_V58_IMPLEMENTATION_MAPPING_v0.md`

## Carry Forward Nearly As-Is

- shipped `V56-B` action-class, runtime-state, and ticket semantics
- shipped `V57-A` observation and local-effect conformance semantics
- shipped `V58-A` / `V58-B` live-turn admission / handoff / reintegration lineage
- shipped `V58-C` advisory hardening posture as shaping input only
- the rule that prior workspace state is context at most, never sufficient authority

## Re-Author With Repo Alignment

`V59-A` should add exactly:

- `agentic_de_workspace_continuity_region_declaration@1`
- `agentic_de_workspace_continuity_admission_record@1`
- `agentic_de_workspace_occupancy_report@1`
- `agentic_de_workspace_continuity_reintegration_report@1`

`V59-A` should consume:

- one current URM copilot session path
- one explicit `agentic_de_lane_drift_record@1`
- shipped `V56-A` / `V56-B` packet / proposal / checkpoint / ticket surfaces
- shipped `V57-A` observation / local-effect conformance surfaces
- shipped `V58-A` / `V58-B` live-turn admission / handoff / reintegration surfaces
- committed closeout evidence from shipped `V56` / `V57` / `V58` lanes as drift guard
  only

Those prior committed artifacts should outrank narrative interpretation for drift
checking, but they should not count as current-turn continuity witness.

`V59-A` should keep the ordering explicit:

- continuity admission is an additional gate over carried-forward state
- it does not replace shipped `V58` current-turn live admission
- continuity reintegration wraps around the already ordered `V58` / `V56` / `V57`
  governed act rather than reordering it

## Starter Continuity Law

The starter continuity turn should make these laws explicit:

- current-turn live admission remains required
- the continuity region must be explicitly declared, not inferred from non-reset
  runtime state
- continuity admission must remain typed and replayable:
  - same selected continuity evidence chain
  - same frozen policy
  - same continuity verdict
- any continuity verdict other than `admitted` remains non-entitling and fail-closed
  in this slice
- prior workspace state may inform continuity admission only as:
  - carried-forward state
  - lineage context
  - drift context
  - declared continuity witness
- none of those categories is current-turn native witness by default
- `create_new` remains admissible only when the target occupancy verdict is
  `unoccupied`
- occupied or drifted state may not be silently normalized into starter admissibility
- prior successful turn, prior ticket, and prior reintegration do not become ambient
  admissibility for the next turn
- positive continuity reintegration requires explicit witness basis or certificate ref
- restoration is not selected in this slice
- replay / resume widening is not selected in this slice

The selected continuity path in this slice should remain exactly:

- live session path:
  - URM copilot session path already selected by `V58`
- action class:
  - `local_write`
- write kind:
  - `create_new`
- declared continuity root:
  - `artifacts/agentic_de/v59/workspace_continuity/`
- exact starter target centered on:
  - `runtime/reference_patch_candidate.diff`

## Required Axes

`agentic_de_workspace_continuity_region_declaration@1` should at minimum externalize:

- continuity region id
- declared continuity root
- exact target set or target identity
- allowed write-kind subset
- occupancy policy
- region origin tags

`agentic_de_workspace_continuity_admission_record@1` should at minimum externalize:

- live-turn admission ref
- live-turn handoff ref
- continuity region declaration ref
- current-turn continuity verdict
- continuity reason codes
- continuity snapshot summary
- current repo root / cwd
- current continuity-root identity
- source-origin tags for authority-bearing fields
- dependence tags when any field is derived rather than native current-turn support

At minimum the starter slice should distinguish continuity verdicts such as:

- admitted
- region_mismatch
- rejected_inadmissible
- stale_continuity_basis
- unresolved_drift
- withheld_by_policy
- unknown

`agentic_de_workspace_occupancy_report@1` should at minimum externalize:

- continuity admission ref
- target relative path
- occupancy verdict
- prior governed-lineage ref when matched
- drift posture summary
- out-of-band evidence summary when applicable
- occupancy witness basis summary
- source-origin tags
- dependence tags
- root-origin identifiers needed for dedup / non-independence checks

At minimum the starter slice should distinguish occupancy verdicts:

- `unoccupied`
- `occupied_prior_governed_exact`
- `occupied_prior_governed_drifted`
- `occupied_out_of_band`
- `occupied_unknown`

The occupancy checker should remain witness-bearing and replayable.

At minimum the starter slice should require:

- declared continuity snapshot identity;
- target-level presence or absence inside the declared region;
- prior governed artifact refs when a prior governed match is asserted;
- root-origin linkage when prior governed lineage is claimed; and
- explicit out-of-band detection grounds when out-of-band occupancy is asserted.

The same selected occupancy evidence chain plus the same frozen policy must yield the
same occupancy verdict.

Non-target occupants already present inside the declared continuity root should remain
explicitly scoped in this slice:

- recorded only as region-scope context or out-of-scope drift;
- not treated as target entitlement;
- not treated as ambient admissibility by their mere presence.

`agentic_de_workspace_continuity_reintegration_report@1` should at minimum externalize:

- live-turn_reintegration_ref
- continuity admission ref
- occupancy report ref
- observation ref
- local-effect conformance ref
- observed effect summary
- continuity reintegration status
- continuity reintegration reason codes
- continuity witness basis summary
- continuity witness certificate ref or equivalent witness ref when positive
  reintegration is asserted
- continuity-region state summary after the act
- source-origin tags for carried-forward versus current-turn native material
- dependence tags for any derived component
- root-origin dedup summary for repeated observability or prior-artifact inputs

## Defer To Later Slice

- explicit continuity-safe restoration
- continuity hardening / migration
- second target or broader target set
- append-only, overwrite, or destructive continuity semantics

## Do Not Import

- implicit continuity by ceasing reset alone
- occupied target silently treated as `create_new`
- prior ticket or prior reintegration as standing authority
- out-of-band drift treated as native current-turn witness
- restoration or replay semantics under continuity
