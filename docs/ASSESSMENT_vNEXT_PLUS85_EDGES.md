# Assessment vNext+85 Edges

Status: planning-edge assessment for `V41-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS85_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Ambient Repo Read Drift

- Risk:
  observation could claim to analyze the released request scope while actually reading
  files outside the released `source_set` or outside the released repo boundary.
- Response:
  require exact request-bound provenance closure for every observed entry and fail
  closed on any provenance ref outside the released request world.

### Edge 2: Observation / Intended Collapse

- Risk:
  the observed lane could start emitting intended architecture truth, deontic
  settlement, or semantic interpretations under the cover of “implementation facts.”
- Response:
  keep `adeu_architecture_observation_frame@1` facts-only and reject intended
  semantics, settlement vocabulary, and alignment judgment inside the observed lane.

### Edge 3: Settlement Posture Laundering

- Risk:
  observation could consume a blocked settlement frame and then silently behave as if
  downstream compile were now entitled.
- Response:
  allow observation to consume the released settlement frame, but forbid it from
  upgrading, reinterpreting, or erasing upstream `compile_entitlement` posture.

### Edge 4: Provenance-Light / Mushy Observation Entries

- Risk:
  the frame could look typed at the top level while actual evidence for observed
  units, boundaries, workflows, and hooks hides in semi-structured blobs.
- Response:
  require every observed entry to remain explicitly addressable and provenance-linked
  through ids, `fact_kind`, `observation_mode`, source refs, and minimal typed
  fields so the lane does not collapse into provenance-linked prose summaries.

### Edge 5: Silent Invention Instead Of Unresolved Observation

- Risk:
  missing code facts could be silently filled in, creating a polished but false
  observation frame.
- Response:
  require explicit `unresolved_observations` with `unresolved_reason_kind`,
  rationale, and source support rather than silent defaults or invented structure.

### Edge 6: Alignment / Remediation Creep

- Risk:
  `V41-C` could start reporting drift, severity, or repair advice under the cover of
  “observed implementation context.”
- Response:
  keep alignment, intended compile, and remediation out of scope and reject such
  fields in the observation frame.

### Edge 7: Direct vs Derived Extraction Blur

- Risk:
  later intended/alignment lanes could not tell whether an observed fact came
  straight from source text or from a bounded extraction heuristic, making mismatch
  analysis harder and laundering derived structure as raw observation.
- Response:
  require every resolved observed entry to declare `observation_mode = direct |
  derived` and keep derived structure bounded to provenance-linked extraction over
  the released request world.

### Edge 8: Settlement Carry-Through Drift

- Risk:
  downstream consumers could be forced to reopen settlement artifacts just to know
  what entitlement posture the observation frame was produced under, or worse, the
  observed frame could silently drop blocking lineage.
- Response:
  carry forward `upstream_compile_entitlement` plus explicit
  `upstream_blocking_refs` from the released settlement frame and reject drift.

### Edge 9: Floating Cross-Entry Structure

- Risk:
  workflow `step_refs` or boundary `crossing_refs` could form an internally
  referential graph that is only weakly grounded in actual repo files.
- Response:
  require all cross-entry refs to resolve to typed in-frame observation entries and
  forbid cross-entry structure that lacks concrete `source_ref` anchoring.

### Edge 10: Duplicate Or Ambiguous Observation Identity

- Risk:
  root-local ids could collide, making later intended/alignment lanes ambiguous about
  which observed entry is authoritative.
- Response:
  require uniqueness for root-local observation ids and fail closed on duplicates.

## Current Judgment

- `V41-C` is worth implementing now because `V41-A` already froze the repo world and
  `V41-B` already froze the interpretive/entitlement seam; the next missing layer is
  exactly the bounded observed implementation frame that later intended and alignment
  slices must consume without collapsing lane boundaries.
