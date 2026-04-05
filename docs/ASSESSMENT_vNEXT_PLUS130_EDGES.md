# Assessment vNext+130 Edges

Status: post-closeout edge assessment for `V52-D` (April 5, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS130_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Visualization Becomes Second Semantic Owner

- Risk:
  the spatial scene could start inventing semantic meaning locally instead of behaving
  as a bounded presentation layer over released paper-semantic artifacts.
- Response:
  derive scene state only from released claims, lane fragments, inference bridges, and
  released ordering anchors; forbid renderer-minted semantic authority.
- Closeout Evidence:
  `buildSpatialScene(...)` in
  `apps/web/src/app/papers/semantic-workbench/view-model.ts` derives scene state only
  from released artifact payloads, while semantic-law fields remain visible in the
  route-local view model and client panels.

### Edge 2: Prototype Spatial Scene Laundering

- Risk:
  the imported prototype `spatial-lane-scene.tsx` could become de facto live
  authority by copy-over rather than by repo-owned re-authoring.
- Response:
  use the prototype scene as shaping evidence only and re-author the live scene under
  repo-native `apps/web/src/app/papers/semantic-workbench/`.
- Closeout Evidence:
  shipped scene code exists in
  `apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx`, while route
  tests still forbid direct imports from the external prototype overlay.

### Edge 3: Browser Trigger Drift Into `V52-C`

- Risk:
  the visualization slice could quietly become a browser-triggered live worker seam
  instead of remaining a presentation extension of the released workbench route.
- Response:
  keep `V52-D` fetch-free and worker-trigger-free; `V52-C` remains accepted context
  only, not browser authority.
- Closeout Evidence:
  import/fetch guards in
  `apps/web/tests/paper-semantic-workbench-contract.test.ts` still forbid `fetch`,
  `api-base`, and live-worker imports in the route tree.

### Edge 4: Spatial Surface Mistaken For Released Projection Surface

- Risk:
  the route could treat `spatial` as if it were a required released
  `projection.surface` value and either reject valid artifacts or silently mint a new
  released projection contract.
- Response:
  keep `spatial` route-local and derived only, with released `artifact` / `local`
  projections remaining authoritative ordering anchors.
- Closeout Evidence:
  `parsePaperSemanticProjection(...)` still admits only released `artifact` / `local`
  values, while `selectSpatialOrderingProjection(...)` derives `spatial` ordering from
  those released anchors and fails closed otherwise.

### Edge 5: Scene Layout Nondeterminism

- Risk:
  node position or ordering could drift by implementation taste and make `scene_hash`
  unstable over the same released artifact.
- Response:
  freeze deterministic lane-column and claim-row layout law with no physics,
  randomness, or implementation-defined force layout.
- Closeout Evidence:
  deterministic positioning and `computeStableSceneHash(...)` are implemented in
  `view-model.ts`, and repeated-view-model regression coverage in
  `apps/web/tests/paper-semantic-workbench-contract.test.ts` confirms stable
  `scene_hash` / `node_order`.

### Edge 6: 3D Rendering Intent Fails To Materialize

- Risk:
  route-local `translateZ(...)` posture could exist in code while the rendered scene
  remains flat because the viewport never establishes 3D context.
- Response:
  keep 3D posture explicit in route-local CSS only:
  - `perspective`
  - `transform-style: preserve-3d`
- Closeout Evidence:
  review hardening landed in `page.module.css` via merged follow-up commit
  `02fd0e4`, adding both `perspective: 1200px` and `transform-style: preserve-3d`.

### Edge 7: Scene Construction Drifts Into Avoidable Scan Cost

- Risk:
  the deterministic scene builder could remain correct but become increasingly costly
  as artifacts grow because it repeatedly scans claims/fragments in nested loops.
- Response:
  keep the same deterministic law while using route-local lookup maps and grouped
  fragments.
- Closeout Evidence:
  merged follow-up commit `02fd0e4` replaces repeated `find` / `filter` scans in
  `buildSpatialScene(...)` with claim/fragments lookup maps without changing node
  order or scene semantics.

### Edge 8: Build And Runtime Portability Drift

- Risk:
  a route-local scene can pass narrow contract tests yet fail real web build/runtime
  constraints through unsupported imports or excessive route-level infra.
- Response:
  validate the bounded route through the live `apps/web` lint/test/build lane and keep
  implementation route-local.
- Closeout Evidence:
  bounded `apps/web` lint, route contract test, route smoke test, and `next build`
  all passed before merge, and the merged `web` CI check stayed green on PR `#352`.

## Current Judgment

- `V52-D` was the right final D-track move because it internalized the imported
  paper-workbench overlay’s spatial/morphic idea without reopening paper semantic
  authority, worker ownership, or browser-trigger semantics.
- the shipped result remains properly bounded: one route-local `spatial` surface
  only, one deterministic scene model only, one scene component only, one same-object
  transition posture only, and no fetch / worker trigger / API widening.
- the release also stayed subordinate to released `V52-A` semantics and released
  `V52-B` workbench ordering anchors rather than inventing a second semantic layer.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` through
  `V52-D` closed on `main` and no further internal `V52` path currently selected.
