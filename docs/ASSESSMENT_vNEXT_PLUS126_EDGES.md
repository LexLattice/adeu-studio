# Assessment vNext+126 Edges

Status: post-closeout edge assessment for `V51-C` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS126_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Web Layer Becomes Second API/KERNEL Owner

- Risk:
  `apps/web` could reintroduce simulation or route semantics locally and stop behaving
  like a bounded consumer.
- Response:
  keep the route subordinate to released `POST /odeu-sim/run` and keep direct kernel
  imports out of `apps/web`.
- Closeout Evidence:
  `apps/web/src/app/odeu-sim/odeu-sim-client.tsx`,
  `apps/web/src/app/odeu-sim/view-model.ts`, and the no-kernel-import contract test in
  `apps/web/tests/odeu-sim-contract.test.ts`.

### Edge 2: Prototype Control-Surface Laundering

- Risk:
  the imported static sandbox controls could reappear as reset/step/start/pause or
  override sliders in the first web slice.
- Response:
  freeze `V51-C` as one summary-first browser route and forbid stepwise controls and
  override grids.
- Closeout Evidence:
  shipped route scope limited to `/odeu-sim`, route-local support modules/tests, and
  the absence of prototype-style control surfaces in `apps/web/src/app/odeu-sim/`.

### Edge 3: Browser Persistence Drift

- Risk:
  the first web slice could quietly introduce `localStorage`, `sessionStorage`, or
  other persistent client state.
- Response:
  keep the route stateless and non-persistent in the browser.
- Closeout Evidence:
  `apps/web/src/app/odeu-sim/odeu-sim-client.tsx` uses local React component state
  only and ships no storage adapter or browser persistence hook.

### Edge 4: Initial Auto-Run Drift

- Risk:
  the first web slice could auto-run the default scenario on page load and blur the
  difference between idle rendering and user-triggered execution.
- Response:
  freeze the initial interaction law as idle-first with defaults prefilled and
  user-triggered run only.
- Closeout Evidence:
  `INITIAL_ROUTE_STATUS = "idle"`, `buildDefaultViewConfig()`, the submit-only fetch
  path in `handleSubmit(...)`, and the idle-only empty-panel rendering.

### Edge 5: Renderer Semantic Reinterpretation

- Risk:
  the route could reinterpret regime labels, lane semantics, or action meaning instead
  of rendering released API facts.
- Response:
  freeze the route to render released response fields only and forbid renderer-level
  semantic minting.
- Closeout Evidence:
  `createViewModelFromApiResponse(...)` in `view-model.ts`, direct rendering of
  released fields in `odeu-sim-client.tsx`, and absence of any second semantic
  judgment layer in the shipped route.

### Edge 6: Projection Widening Drift

- Risk:
  the UI could widen from summary rendering into network graphs, trace-heavy panels,
  or broader sandbox detail before the route seam is accepted.
- Response:
  keep the bounded rendered sections explicit and reject the prototype’s wider
  visualization surface in this slice.
- Closeout Evidence:
  shipped panels limited to response identity, lane summary, action counts, observed
  counts, config snapshot, current metric, and one failure banner.

### Edge 7: Status-Mapping Drift

- Risk:
  the web route could invent a different success/failure status model instead of
  carrying the released API statuses through one bounded UI mapping.
- Response:
  freeze exact mapping from API `request_status` into UI `route_status`, with only
  `idle` and `loading` added locally.
- Closeout Evidence:
  `mapApiRequestStatusToRouteStatus(...)` in `view-model.ts` and
  `test("odeu sim view-model: API status maps directly after completion")`.

### Edge 8: Deterministic Render Drift

- Risk:
  the same released response could render differently across repeated runs because the
  route leaves ordering or state handling implicit.
- Response:
  keep deterministic route-smoke and minimal interaction checks over the bounded
  response projection.
- Closeout Evidence:
  `apps/web/tests/routes.smoke.test.mjs`, stable sparse action-count rendering from
  released API payloads, and bounded contract tests over the released fixture set.

### Edge 9: Failure Rendering Drift

- Risk:
  typed fail-closed API responses could be hidden, normalized away, or treated as
  generic browser errors.
- Response:
  render explicit failure posture for released `fail_closed_invalid_request` and
  `fail_closed_kernel_mismatch` statuses.
- Closeout Evidence:
  `failureMessageForStatus(...)`, failure-banner rendering in `OdeuSimClient`, and the
  kernel-mismatch fixture contract test.

### Edge 10: Product-Surface Creep

- Risk:
  one bounded route could turn into broader product-wide routing, navigation, or
  simulation entitlement.
- Response:
  keep `V51-C` bounded to `/odeu-sim`, route-local support modules, and targeted web
  tests only.
- Closeout Evidence:
  shipped scope limited to `apps/web/src/app/odeu-sim/*`,
  `apps/web/tests/odeu-sim-contract.test.ts`,
  `apps/web/tests/routes.smoke.test.mjs`, and closeout artifacts only.

### Edge 11: No-Kernel-Import Boundary Drift

- Risk:
  `apps/web` could quietly import `adeu_odeu_sim` directly and collapse the intended
  API-consumer boundary.
- Response:
  keep one enforceable no-kernel-import acceptance check over
  `apps/web/src/app/odeu-sim/`.
- Closeout Evidence:
  `test("odeu sim route: no direct kernel import under apps/web/src/app/odeu-sim")`
  with hardened side-effect and subpath import detection.

### Edge 12: Prototype UI Precedent Laundering

- Risk:
  the imported `static/index.html`, `static/app.js`, or `static/style.css` could be
  copied into live paths wholesale and treated as released authority.
- Response:
  re-author the web route in repo-native Next.js paths and keep the prototype static
  surface as shaping evidence only.
- Closeout Evidence:
  shipped code exists only under `apps/web/src/app/odeu-sim`, while the imported
  bundle remains under `examples/external_prototypes/odeu-sandbox-app`.

## Current Judgment

- `V51-C` was the right third C-track move because it exposed the released kernel/API
  stack through one narrow browser consumer without reopening simulation law in
  `apps/web`.
- the shipped result is properly bounded: one `/odeu-sim` route, idle defaults with
  user-triggered run only, direct API request-status carriage, full released
  `config_snapshot` and `current_metric`, exact three-key lane summary, sparse
  observed-only action counts, explicit fail-closed banners, and no reset/step/state
  controls, network graph, event trace, or persistent browser state.
- review hardening materially improved the release: the idle panel no longer appears
  in loading/failure states, repo-root discovery in the contract test now fails
  closed, and the import-ban matcher now catches side-effect and subpath imports.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` should now be read with `V51-A` through
  `V51-C` closed on `main` and no further internal `V51` path selected.
