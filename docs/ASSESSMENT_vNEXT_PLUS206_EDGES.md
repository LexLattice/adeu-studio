# Assessment vNext+206 Edges

Status: planning-edge assessment for `V74-A`.

Authority layer: pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS206_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Projection Could Become Authority

- Risk:
  operator case views could be read as ratification, adoption, release, product,
  runtime, dispatch, or source truth.
- Response:
  require non-authority guardrails, visible authority state, and forbidden
  projection authority lists on every accepted case.

### Edge 2: Ready For Human Review Could Become Permission To Act

- Risk:
  `ready_for_human_review` could be overread as permission for the operator to
  implement, ratify, release, productize, or dispatch.
- Response:
  require `projection_horizon` and `visible_authority_state` fields so
  visibility remains separate from authority to act.

### Edge 3: Blockers Could Be Hidden Until V74-B

- Risk:
  `V74-A` could reference exceptions without a machine-checkable shape until
  the later exception register exists.
- Response:
  embed minimal visible blocker / exception-summary rows in the case-view
  payload and require source-bound blocker refs.

### Edge 4: Product Wedge Could Become Product Authorization

- Risk:
  the typed-adjudication product-pressure case could be projected as product
  selection or product authorization.
- Response:
  require product-pressure cases to carry product-authority-missing posture
  unless rejected or out of scope, and reject product-authorized projection.

### Edge 5: Model Comparison Could Become Benchmark Truth

- Risk:
  a model-output comparison case could imply global model ranking or future
  model selection.
- Response:
  `V74-A` may only project the case kind; comparison axes and detailed
  adjudication remain deferred to `V74-B`, and benchmark truth claims reject.

### Edge 6: Source Absence Could Be Repaired By Prose

- Risk:
  missing support, dogfood, or `V73-C` sources could be silently filled from
  planning memory.
- Response:
  require concrete projection source rows or explicit absence posture.

### Edge 7: Operator Interaction Could Become Command Surface

- Risk:
  projection language could imply a live button, command action, runtime
  permission, or dispatch path.
- Response:
  `V74-A` does not implement operator actions; allowed action posture remains
  inspect / acknowledge / request-later-review style only.

### Edge 8: V74-A Could Begin V74-B Or V74-C

- Risk:
  starter implementation could include typed adjudication projection,
  comparison axes, exception register, visibility contract, workbench
  projection, or post-projection handoff.
- Response:
  keep `V74-A` to case view, source index, blocker summaries, and
  non-authority guardrails only.

### Edge 9: V75 Handoff Could Be Smuggled In Early

- Risk:
  a projected later-dispatch need could be represented as dispatch readiness.
- Response:
  no post-projection handoff lands in `V74-A`; any later `V75` request is
  deferred to `V74-C`.

### Edge 10: External Contest Or Product Surface Could Bypass The Ladder

- Risk:
  product or external contest pressure could use projection visibility to skip
  later family review.
- Response:
  keep product authorization, external contest participation, runtime
  permission, and dispatch forbidden in the `V74-A` guardrail.

## Current Judgment

- `V74-A` is worth implementing next because closed `V73` can now emit
  recommendation and operator-cognition substrate, but the repo still lacks a
  governed way to project that substrate to the operator without authority
  laundering.
- The starter slice is bounded enough to activate after this docs bundle:
  three repo-description schemas, source-bound fixtures, visible blocker
  summaries, and explicit non-authority guardrails.
