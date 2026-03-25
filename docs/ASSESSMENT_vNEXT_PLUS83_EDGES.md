# Assessment vNext+83 Edges

Status: planning-edge assessment for `V41-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS83_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Working-Tree Determinism Drift

- Risk:
  the first practical slice could treat ambient working-tree state as if it were a
  replay-stable source universe.
- Response:
  freeze `committed_tree` and explicit `materialized_snapshot` as the only lawful
  snapshot modes in `V41-A`, and require immutable snapshot identity for the chosen
  mode.

### Edge 2: Scope Laundering Through Vague Selection

- Risk:
  "real repo scope" could remain soft prose and let later slices choose different
  worlds under the same request id.
- Response:
  require one subtree anchor plus explicit additions, exclusions, and artifact-kind
  policy inside the typed request.

### Edge 3: Source-Set Provenance Underspecification

- Risk:
  a global hash alone could hide which exact files were analyzed, making later
  observation and intended compile provenance weaker than the rest of the family.
- Response:
  require per-item path/kind/hash records plus one aggregate `source_set_hash`, with
  canonical ordering fixed to normalized repo-relative path order.

### Edge 4: Brief-World Drift Outside The Frozen Repo World

- Risk:
  the repo world could be deterministic while maintainer brief inputs still float
  outside the captured request boundary.
- Response:
  require `maintainer_brief_refs` and `accepted_doc_refs` to resolve either to frozen
  `source_set` content or to separately materialized and hashed artifacts captured by
  the request.

### Edge 5: Authority-Policy Drift At Request Time

- Risk:
  the practical loop could postpone authority-boundary pinning until later slices and
  thereby let the request boundary itself drift.
- Response:
  bind exact `authority_boundary_policy` or exact policy ref inside
  `adeu_architecture_analysis_request@1`.

### Edge 6: Settlement Leak Into Request Capture

- Risk:
  `V41-A` could overreach by smuggling chosen interpretation, entitlement posture, or
  drift claims into the request lane before the explicit settlement slice exists.
- Response:
  keep only settlement hooks in the request and fail closed on settlement,
  impossibility, or drift authority claims in this arc.

### Edge 7: Observation Creep

- Risk:
  the first practical slice could start extracting observed code facts under the cover
  of "source-set capture", mixing capture and observation into one lock.
- Response:
  keep `V41-A` bounded to request and source-set materialization only; observed
  implementation remains the next-but-one seam.

### Edge 8: Repo-Scale Overreach

- Risk:
  the first practical slice could target too much of a repo and make deterministic
  replay fragile or expensive before the pipeline has been exercised on one bounded
  internal scope.
- Response:
  keep the accepted fixture tied to one bounded internal subtree plus explicit file
  additions only where necessary.

## Current Judgment

- `V41-A` is worth implementing now because it freezes the exact repo world, request
  inputs, and authority-policy pinning that every later practical-analysis lane will
  rely on.
