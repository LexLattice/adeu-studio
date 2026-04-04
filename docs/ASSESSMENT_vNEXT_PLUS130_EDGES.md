# Assessment vNext+130 Edges

Status: planning-edge assessment for `V52-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS130_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
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

### Edge 2: Prototype Spatial Scene Laundering

- Risk:
  the imported prototype `spatial-lane-scene.tsx` could become de facto live
  authority by copy-over rather than by repo-owned re-authoring.
- Response:
  use the prototype scene as shaping evidence only and re-author the live scene under
  repo-native `apps/web/src/app/papers/semantic-workbench/`.

### Edge 3: Browser Trigger Drift Into `V52-C`

- Risk:
  the visualization slice could quietly become a browser-triggered live worker seam
  instead of remaining a presentation extension of the released workbench route.
- Response:
  keep `V52-D` fetch-free and worker-trigger-free; `V52-C` remains accepted context
  only, not browser authority.

### Edge 4: Scene Projection Drift

- Risk:
  unsupported node kinds, edge kinds, or missing projection dependencies could be
  silently repaired and hide real contract mismatch.
- Response:
  freeze bounded scene vocabularies and fail closed on projection mismatch or
  unsupported values.

### Edge 4A: Spatial Surface Mistaken For Released Projection Surface

- Risk:
  the route could treat `spatial` as if it were a required released
  `projection.surface` value and either reject valid artifacts or silently mint a new
  released projection contract.
- Response:
  keep `spatial` route-local and derived only, with released `artifact` / `local`
  projections remaining authoritative ordering anchors.

### Edge 4B: Scene Layout Nondeterminism

- Risk:
  node position or ordering could drift by implementation taste and make `scene_hash`
  unstable over the same released artifact.
- Response:
  freeze deterministic lane-column and claim-row layout law with no physics,
  randomness, or implementation-defined force layout.

### Edge 5: Morphic Transition Sprawl

- Risk:
  richer transitions could turn into a second product/navigation layer instead of
  same-object route-local transitions.
- Response:
  keep `V52-D` bounded to the existing route and freeze same-object transitions across
  `artifact`, `local`, and `spatial` only.

### Edge 6: Build And Runtime Portability Drift

- Risk:
  a route-local scene can pass narrow contract tests yet fail real web build/runtime
  constraints through unsupported imports or excessive route-level infra.
- Response:
  validate the bounded route through the live `apps/web` lint/test/build lane and keep
  implementation route-local.

## Current Judgment

- `V52-D` is worth implementing next because it is the final bounded family seam that
  can internalize the imported prototype’s spatial/morphic idea without reopening
  semantic authority or bridge ownership.
- the slice should stay route-local, artifact-subordinate, and explicit that the
  scene is presentation only over released `V52-A` artifacts and the already accepted
  `V52-B` workbench model.
- it should also stay explicit that `spatial` is a route-local derived surface rather
  than a new released projection surface on the paper-semantic artifacts.
- it should also stay explicit that `V52-C` remains a separate live worker seam and is
  not browser-triggered by this visualization slice.
