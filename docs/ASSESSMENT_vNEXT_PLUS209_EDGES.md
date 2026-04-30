# Assessment vNext+209 Edges

Status: pre-lock edge assessment for `V75-A` (May 1, 2026 UTC).

Authority layer: planning / pre-start scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS209_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Dispatch Review Could Become Dispatch

- Containment:
  `V75-A` emits dispatch-review request, source index, and non-execution
  guardrail rows only.
- Required proof:
  reject fixtures for worker assignment, command execution, and dispatch
  claims.

### Edge 2: Support Context Could Become Eligibility Source

- Containment:
  `eligible_for_dispatch_review` requires released `V74-C` handoff, visibility
  contract, and workbench projection source roles.
- Required proof:
  reject fixture where support / roadmap / review sources are the only
  eligibility sources.

### Edge 3: Upstream Exceptions Could Float Free

- Containment:
  `V75-A` carries upstream `V74-C` exception refs with explicit exception
  origin; native dispatch exceptions are deferred to `V75-B`.
- Required proof:
  reject fixture for native `V75-B` exception refs or exception refs without
  origin in `V75-A`.

### Edge 4: Required Later Authority Could Become Prose

- Containment:
  runtime, product, release, external, dispatch-execution, human / maintainer,
  and recursive-policy authority gaps must use row-shaped authority
  requirements.
- Required proof:
  reject fixture for free-floating later-authority claims.

### Edge 5: Product Or Runtime Pressure Could Be Smuggled Into Dispatch

- Containment:
  product, runtime, release, and external branch authority gaps block or defer
  dispatch-review requests unless a later selected family handles them.
- Required proof:
  reject fixtures for product dispatch laundering and runtime command
  laundering.

### Edge 6: Workbench Projection Could Become Authorization

- Containment:
  `V75-A` can consume workbench projection rows as sources, but cannot treat
  workbench actions as authorization.
- Required proof:
  reject fixture for workbench action as dispatch authority.

### Edge 7: Guardrails Could Become Empty Labels

- Containment:
  non-execution guardrails require non-empty forbidden action kinds.
- Required proof:
  reject fixture for empty guardrail forbidden action kinds.

### Edge 8: V75-A Could Begin V75-B Or V75-C

- Containment:
  worker role profiles, assignment plans, IO contracts, tool matrices,
  dispatch exception registers, reconciliation plans, reconciliation contracts,
  post-dispatch-review handoffs, and family closeout alignment remain deferred.
- Required proof:
  tests or fixtures proving `V75-A` rows do not emit later-slice surfaces.

### Edge 9: External Branch Could Sneak In

- Containment:
  external contest pressure remains blocked or future-family-only unless `V43`
  branch posture is selected by a later authority surface.
- Required proof:
  reject fixture for external contest pressure without `V43` branch posture.

## Residual Edges

- `V75-B` must later keep worker role, assignment, IO, tool, and exception
  posture non-executing.
- `V75-C` must later keep output reconciliation non-truth and
  post-dispatch-review handoff distinct from dispatch execution.
- Runtime permission, productized typed adjudication, external contest
  participation, graph / memory, cross-corpus governance, and recursive
  experiment authority remain mapped but unselected.

## Pre-Lock Judgment

- `V75-A` is appropriately scoped as a bounded dispatch-review starter slice.
- The starter may create source-bound request and guardrail substrate only.
- The highest-risk seams are source eligibility, upstream exception origin,
  row-shaped later authority, workbench action laundering, and dispatch /
  runtime / product / external authority laundering.
