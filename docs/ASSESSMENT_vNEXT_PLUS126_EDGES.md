# Assessment vNext+126 Edges

Status: pre-lock edge assessment for `V51-C` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS126_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Web Layer Becomes Second API/KERNEL Owner

- Risk:
  `apps/web` could reintroduce simulation or route semantics locally and stop behaving
  like a bounded consumer.
- Planned Response:
  require the route to consume the released `POST /odeu-sim/run` surface only and keep
  direct kernel imports out of `apps/web`.

### Edge 2: Prototype Control-Surface Laundering

- Risk:
  the imported static sandbox controls could reappear as reset/step/start/pause or
  override sliders in the first web slice.
- Planned Response:
  freeze `V51-C` as one summary-first browser route and forbid stepwise controls and
  override grids.

### Edge 3: Browser Persistence Drift

- Risk:
  the first web slice could quietly introduce `localStorage`, `sessionStorage`, or
  other persistent client state.
- Planned Response:
  keep the route stateless and non-persistent in the browser.

### Edge 4: Initial Auto-Run Drift

- Risk:
  the first web slice could auto-run the default scenario on page load and blur the
  difference between idle rendering and user-triggered execution.
- Planned Response:
  freeze the initial interaction law as idle-first with defaults prefilled and
  user-triggered run only.

### Edge 5: Renderer Semantic Reinterpretation

- Risk:
  the route could reinterpret regime labels, lane semantics, or action meaning instead
  of rendering released API facts.
- Planned Response:
  freeze the route to render released response fields only and forbid renderer-level
  semantic minting.

### Edge 6: Projection Widening Drift

- Risk:
  the UI could widen from summary rendering into network graphs, trace-heavy panels,
  or broader sandbox detail before the route seam is accepted.
- Planned Response:
  keep the bounded rendered sections explicit and reject the prototype’s wider
  visualization surface in this slice.

### Edge 7: Status-Mapping Drift

- Risk:
  the web route could invent a different success/failure status model instead of
  carrying the released API statuses through one bounded UI mapping.
- Planned Response:
  freeze exact mapping from API `request_status` into UI `route_status`, with only
  `idle` and `loading` added locally.

### Edge 8: Deterministic Render Drift

- Risk:
  the same released response could render differently across repeated runs because the
  route leaves ordering or state handling implicit.
- Planned Response:
  keep deterministic route-smoke and minimal interaction checks over the bounded
  response projection.

### Edge 9: Failure Rendering Drift

- Risk:
  typed fail-closed API responses could be hidden, normalized away, or treated as
  generic browser errors.
- Planned Response:
  render explicit failure posture for released `fail_closed_invalid_request` and
  `fail_closed_kernel_mismatch` statuses.

### Edge 10: Product-Surface Creep

- Risk:
  one bounded route could turn into broader product-wide routing, navigation, or
  simulation entitlement.
- Planned Response:
  keep `V51-C` bounded to `/odeu-sim`, route-local support modules, and targeted web
  tests only.

### Edge 11: No-Kernel-Import Boundary Drift

- Risk:
  `apps/web` could quietly import `adeu_odeu_sim` directly and collapse the intended
  API-consumer boundary.
- Planned Response:
  add one enforceable no-kernel-import acceptance check over
  `apps/web/src/app/odeu-sim/`.

### Edge 12: Prototype UI Precedent Laundering

- Risk:
  the imported `static/index.html`, `static/app.js`, or `static/style.css` could be
  copied into live paths wholesale and treated as released authority.
- Planned Response:
  re-author the web route in repo-native Next.js paths and keep the prototype static
  surface as shaping evidence only.
