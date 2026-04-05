# Draft Stop-Gate Decision vNext+130

Status: proposed gate for `V52-D`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS130.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the live route remains exactly `/papers/semantic-workbench`;
- the slice consumes only released `V52-A` artifact data already admitted by the
  released `V52-B` workbench seam;
- the advanced surface widens only to:
  - `spatial`
  - inside the existing route;
- `spatial` is implemented as a route-local derived surface only:
  - released `artifact` / `local` projections remain authoritative ordering anchors
  - no released `projection.surface = spatial` is required;
- the scene projection derives only from released:
  - claims
  - lane fragments
  - inference bridges
  - projection ordering anchors;
- route-local visualization config stays user-driven only:
  - `route_id`
  - `selected_sample_artifact_ref`
  - `selected_surface`
  - `focus_claim_id`
  - `visible_lane_ids`;
- the scene freezes node/edge vocabularies explicitly and fails closed on unsupported
  values;
- the layout/position law is deterministic and explicit:
  - lane columns from released lane order
  - claim rows from released claim order with claim-id fallback only
  - no physics or randomness;
- `artifact` remains the default initial surface and `spatial` is user-selected only;
- the renderer preserves `semantic_hash`, identity/projection field visibility, and
  released authority posture rather than hiding them behind scene-only state;
- no browser-triggered live worker execution, no `fetch`, and no dedicated API route
  ship in this slice;
- no prototype spatial-scene module is imported wholesale into live route code;
- targeted bounded web lint/tests/build pass deterministically.

## Do Not Accept If

- the scene mints new claims, diagnostics, or bridge meanings locally;
- `V52-C` bridge results become browser-authoritative trigger inputs;
- the route widens into upload, pasted-source execution, or live fetch loops;
- the prototype spatial scene is copied wholesale into live route paths;
- advanced visualization is used to justify broader `/papers` product redesign;
- derived view-model state is pushed into route-local config as if it were
  user-controlled authority;
- scene-projection mismatch silently falls back instead of failing closed.

## Local Gate

- docs-only starter validation:
  - `make arc-start-check ARC=130`
- once implementation starts:
  - run the relevant `apps/web` lint/tests/build for the bounded `V52-D`
    visualization surface.
