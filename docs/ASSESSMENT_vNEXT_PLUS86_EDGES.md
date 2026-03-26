# Assessment vNext+86 Edges

Status: planning-edge assessment for `V41-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS86_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Intended / Observed Collapse

- Risk:
  the intended lane could simply mirror observed implementation facts and call that
  intended architecture, erasing the distinction the family was created to preserve.
- Response:
  keep intended and observed as separate artifacts, keep the released request
  boundary plus settlement frame as the normative driver of intended compile, and
  require any observed input to become intended meaning only through explicit
  released root-family structure or else remain ambiguity/advisory posture.

### Edge 2: Blocked Settlement Laundering

- Risk:
  the compile entrypoint could treat the released observation frame as evidence that
  compile may proceed even when the consumed settlement frame remains blocked.
- Response:
  require `compile_entitlement = entitled` for lawful emission and fail closed on any
  blocked settlement or non-empty blocking lineage.

### Edge 3: Repo-World Drift During Intended Compile

- Risk:
  intended compile could claim the released request / settlement / observation world
  while actually consuming a different source universe or free-floating prose.
- Response:
  require exact request/settlement/observation carry-through and fail closed on any
  lineage drift or ambient repo read outside the released request boundary.

### Edge 4: Unresolved Observation Disappearance

- Risk:
  unresolved or derived observed facts could disappear during intended compile,
  creating a polished but unjustifiably settled semantic root.
- Response:
  require unknowns that matter to intended architecture to remain explicit as
  ambiguity or advisory root-family posture rather than vanishing silently, and
  require the accepted fixture ladder to show at least one concrete carry-through
  case.

### Edge 5: Reopening V40-A Schema Authority

- Risk:
  a practical compile slice could quietly redefine the released semantic-root schema
  family while claiming only to materialize repo-grounded instances.
- Response:
  emit only the already-released `V40-A` root-family artifacts and forbid schema
  changes in this slice.

### Edge 6: Alignment / Runner / Downstream Creep

- Risk:
  intended compile could start emitting alignment judgment, runner state, checkpoint
  outputs, projections, or UX surfaces under the cover of “practical analysis.”
- Response:
  keep `V41-D` bounded to repo-grounded intended root-family compile only and reject
  alignment, remediation, runner, checkpoint, projection, and UX surfaces.

### Edge 7: Silent Checkpoint / Oracle Scope Drift

- Risk:
  the broader `V41-D` family plan mentions bounded checkpoint/oracle reuse when
  ambiguity remains, but the first concrete `vNext+86` arc could drift into that
  broader scope without saying so explicitly.
- Response:
  state plainly that `vNext+86` intentionally defers practical checkpoint/oracle
  reuse and emits no repo-grounded checkpoint/oracle artifacts in this first arc.

### Edge 8: Fresh-Brief Universe Drift

- Risk:
  the intended lane could drift into “whatever the maintainer says now” rather than
  compiling over the same frozen `source_set` the request, settlement, and
  observation lanes consumed.
- Response:
  require intended compile to run over the same released request-bound repo world and
  treat free-floating fresh brief input as out of scope.

### Edge 9: Observation-Provenance Escape Hatch

- Risk:
  intended compile could rely on observation entries or summaries that are weakly
  grounded, effectively laundering prose or heuristic output into semantic meaning.
- Response:
  allow observation input only from the released `V41-C` frame and preserve its exact
  request-bound provenance and direct-vs-derived distinction.

## Current Judgment

- `V41-D` is worth implementing now because `V41-A` already froze the repo world,
  `V41-B` already froze interpretation and entitlement, and `V41-C` already froze a
  facts-only observed lane; the next missing layer is exactly the intended compile
  seam that materializes released `V40-A` root-family artifacts over that frozen
  practical boundary.
