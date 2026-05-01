# Assessment vNext+212 Edges

Status: planning-edge assessment for `V76-A`.

Authority layer: pre-lock assessment, not closeout evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS212_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Reconciliation Could Become Truth

- Risk:
  claim maps or relation registers could be overread as proving which worker,
  model, or projected output is correct.
- Response:
  require non-truth guardrails on claim maps and relation rows; reject arbiter
  output as truth, worker output as truth, model output as benchmark truth, and
  majority agreement as correctness.

### Edge 2: Projected Output Could Become Observed Output

- Risk:
  `V75-C` projected output slots could be treated as observed worker outputs
  even though `V75` did not execute dispatch.
- Response:
  preserve `projected_not_observed`; require explicit authorized prior-run or
  support-artifact source posture for any observed worker output refs; add
  `claim_kind` so projected slots can only map slot existence,
  relation-review need, or relation placeholders, not observed output-content
  claims.

### Edge 3: Relation Mapping Could Become Settlement

- Risk:
  relation kinds such as conflict, complementarity, duplicate, orthogonal, or
  single-output/no-relation could be treated as settled conclusions.
- Response:
  keep `V76-A` to mapping / register posture only; defer authority profiles,
  settlement requests, summaries, and handoffs to later `V76` slices.

### Edge 4: Dissent Could Be Smoothed Away

- Risk:
  dissent absence, unknown coverage, warnings, and blockers could be collapsed
  into a single "no dissent" posture.
- Response:
  make dissent presence, search horizon, checked sources, unchecked sources,
  and coverage posture first-class; reject no-dissent claims without a searched
  horizon.

### Edge 5: Product Or Runtime Blockers Could Become Arbiter Readiness

- Risk:
  product pressure or runtime pressure could be rerouted through
  reconciliation as if arbiter review grants downstream authority.
- Response:
  preserve required-later-authority blockers from `V75`; reject conversion of
  product, runtime, release, external branch, dispatch-execution, or
  recursive-policy blockers into readiness.

### Edge 6: V76-A Could Begin V76-B Or V76-C

- Risk:
  the starter could accidentally implement arbiter authority profiles,
  settlement requests, summaries, handoffs, or family closeout alignment.
- Response:
  ship only claim map, relation register, and dissent register surfaces in
  `V76-A`; defer authority, settlement, synthesis, and handoff surfaces.

### Edge 7: Runtime Or Dispatch Could Re-enter Through Reconciliation

- Risk:
  because `V76` consumes dispatch-review rows, reconciliation could be mistaken
  for dispatch execution or runtime permission.
- Response:
  keep all consumed `V75-C` `no_dispatch_executed_by_v75` and non-execution
  guardrails visible; reject command execution, worker assignment, runtime
  permission, PR creation, commit, merge, release, and product authorization.

### Edge 8: Source Context Could Replace Source Rows

- Risk:
  roadmap, support review, or dogfood prose could be used as eligibility
  evidence without concrete released `V75-C` rows.
- Response:
  require source rows over concrete `V75-C` fixtures or explicit absence
  posture; support docs may contextualize but cannot be the only source for a
  claim map.

### Edge 9: Relation Refs Could Become Circular

- Risk:
  claim maps could point to new `V76-A` relation rows while relation rows point
  back to claim maps, making upstream `V75-C` relation evidence ambiguous.
- Response:
  claim maps reference released `V75-C` relation rows through
  `v75_source_relation_refs`; arbiter relation rows separately use
  `source_relation_refs` plus `claim_map_refs`.

### Edge 10: Majority Agreement Could Become Correctness

- Risk:
  several worker or model outputs could agree and be treated as correct without
  source-bound relation review or authority coverage.
- Response:
  reject majority-as-correctness. Agreement can be relation evidence, but it is
  not truth, settlement, ratification, benchmark truth, or model selection.

## Current Judgment

- `V76-A` is worth drafting now because `V75-C` deliberately emitted
  reconciliation / arbiter pressure without executing dispatch or observing
  worker output.
- The first slice should stay narrow: map claim horizons, relation posture, and
  dissent posture over released `V75-C` substrate. It should not settle,
  ratify, execute, productize, release, or dispatch.
