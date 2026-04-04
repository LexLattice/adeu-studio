# Assessment vNext+128 Edges

Status: planning-edge assessment for `V52-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS128_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Browser Layer Becomes Second Semantic Owner

- Risk:
  `apps/web` could start minting paper-semantic meaning locally instead of behaving
  as a bounded consumer of released `V52-A` artifacts.
- Response:
  keep the route subordinate to released `adeu_paper_semantics` artifacts and forbid
  renderer-level semantic reinterpretation.

### Edge 2: Fixture Stack Drift

- Risk:
  the route could silently widen from committed released artifact fixtures into ad hoc
  mock payloads or incomplete projections.
- Response:
  admit only the committed released `V52-A` abstract and paragraph fixtures, validate
  them against the released artifact model before rendering, and fail closed on
  malformed fixture stacks.

### Edge 3: Live Worker / API Laundering

- Risk:
  the mock workbench could quietly become a thin UI over live worker or API behavior,
  collapsing the intended `V52-B` to `V52-C` boundary.
- Response:
  keep `V52-B` read-only and local, with no `fetch`, no worker bridge, and no
  harness/domain registration in the route.

### Edge 4: Existing `/papers` Surface Creep

- Risk:
  the bounded workbench route could turn into a broader retrofit of the existing
  `/papers` route or product navigation surface.
- Response:
  keep `V52-B` bounded to one direct route only and do not treat the existing papers
  page as route-expansion authorization.

### Edge 5: Prototype Visualization Laundering

- Risk:
  the imported spatial-lane scene or broader visualization posture could re-enter as
  first-slice authority.
- Response:
  keep advanced visualization explicitly deferred to `V52-D`.

### Edge 6: Local Ordering / Focus Drift

- Risk:
  the route could leave claim ordering, focus selection, or lane visibility implicit
  and produce unstable read-only projections over the same released artifact.
- Response:
  freeze deterministic local ordering and bounded view-config fields explicitly, using
  released `projection.claim_order` when present and only falling back to claim-id
  order otherwise.

### Edge 7: Identity-Law Visibility Drift

- Risk:
  the route could hide `semantic_hash`, `identity_field_names`, or
  `projection_field_names` and weaken the visible link back to released `V49` /
  `V52-A` semantic law.
- Response:
  keep those identity-law fields visible in the route-local model rather than treating
  them as incidental implementation detail.

### Edge 8: Input-Surface Inflation

- Risk:
  a read-only mock workbench could quietly add pasted text entry, uploads, or
  processing controls before the worker bridge exists.
- Response:
  keep the first web slice committed-sample only, with no text-entry or upload
  surface.

### Edge 9: Overlay Precedent Laundering

- Risk:
  the imported overlay route and helper files could be treated as accepted live
  authority instead of shaping evidence only.
- Response:
  re-author the route in repo-native `apps/web` paths and keep the imported bundle
  support-only and non-precedent.

## Current Judgment

- `V52-B` is worth implementing next because it is the narrowest browser consumer that
  can prove the released `V52-A` contracts are usable in a real domain-facing route
  without widening into live worker execution.
- the slice should stay strictly read-only, committed-sample-backed, and subordinate
  to released `adeu_paper_semantics` artifacts.
