# Assessment vNext+234 Edges

Status: pre-lock edge assessment for `V83-B`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS234_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Edge Decomposition Could Invent Intent

- Starter containment:
  `V83-B` must reference released `V83-A` intent contracts, source rows, and
  guardrails for every decomposition.
- Expected implementation proof:
  edge rows without known intent refs, source refs, or guardrail refs reject.

### Edge 2: Generated Model Or Agent Edge Could Become Authority

- Starter containment:
  generated spec candidates remain candidate-only and must resolve through
  released `V83-A` generation / provenance source rows.
- Expected implementation proof:
  model-output-only edge decomposition rejects unless source-bound intent refs
  and candidate-only provenance are present.

### Edge 3: Semantic Objects Could Become Artifact Obligations Too Early

- Starter containment:
  semantic object rows may carry anticipated artifact kind refs, while actual
  obligations are created only by `repo_artifact_obligation_map@1`.
- Expected implementation proof:
  semantic objects with required implementation changes but no obligation map
  reject or remain blocked.

### Edge 4: Tests Could Become Semantic Preservation

- Starter containment:
  validation needs and acceptance evidence must bind to semantic edges and
  validation rows. Passing tests are not general semantic truth.
- Expected implementation proof:
  test-only preservation and generic passing-test evidence rejects pass.

### Edge 5: Artifact Obligations Could Become Implementation

- Starter containment:
  obligation maps remain non-implementation review records with bounded target
  surface refs. They cannot claim code was changed or is correct.
- Expected implementation proof:
  obligation rows containing implementation, PR, commit, release, or work-
  packet execution claims reject.

### Edge 6: Non-Goals Could Become Required Changes

- Starter containment:
  released `V83-A` non-goal refs remain constraints and must not be mapped as
  required implementation obligations.
- Expected implementation proof:
  non-goal laundering into required change rows rejects.

### Edge 7: Authority Boundaries Could Become Permissions

- Starter containment:
  authority edge rows may constrain obligations but cannot mint runtime,
  product, release, graph-memory, or work-packet authority.
- Expected implementation proof:
  authority boundary converted into permission rejects.

### Edge 8: Broad Targets Could Become Bounded Surfaces

- Starter containment:
  artifact obligation target surfaces must be bounded; broad package/repo/glob
  targets remain blockers or future-family pressure.
- Expected implementation proof:
  broad target surfaces marked ready for projection reject.

### Edge 9: Drift Register Could Resolve Blockers By Prose

- Starter containment:
  drift / ambiguity rows preserve missing source, ambiguity, overbroad target,
  non-goal, authority, Morphic UX, direct OAI, and future-family risks.
- Expected implementation proof:
  blocker rows marked resolved by model prose or support text reject.

### Edge 10: V83-B Could Leak Into V83-C Or V84

- Starter containment:
  `V83-B` selects no projection packet, work-packet handoff, closeout
  alignment, implementation, or later-family selection surfaces.
- Expected implementation proof:
  fixtures containing `V83-C` surfaces, implementation refs, work-packet
  authority, or `V84` selection reject.

## Residual Edges

- `V83-C` must later project released `V83-A` and `V83-B` rows into
  implementation-spec projection packets with provenance, review checklist,
  and quality-gate posture without treating those packets as implementation or
  code correctness.
- Any future implementation work-packet activation family must be selected by
  a later family-level selector after `V83-C` emits source-bound handoff
  pressure.
- Morphic UX, direct OAI, generalized digital artifact projection, product,
  graph-memory, runtime, and release pressures remain contextual or
  future-family-only unless later locks instantiate them.

## Current Judgment

The `vNext+234` starter scope is ready for a bounded `V83-B` implementation
draft. The active implementation should ship only semantic edge decomposition,
artifact obligation maps, and semantic drift / ambiguity registers. The main
risks are invented intent, generated-spec authority drift, test-only semantic
closure, non-goal laundering, authority-boundary laundering, broad target
laundering, and early `V83-C` / `V84` selection; all are represented as
required starter validators and reject fixtures.
