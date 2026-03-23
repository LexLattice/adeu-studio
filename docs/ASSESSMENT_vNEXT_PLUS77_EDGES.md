# Assessment vNext+77 Edges

Status: planning-edge assessment for `V40-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS77_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Root Artifact Catch-All Drift

- Risk:
  the first ASIR root could silently re-accumulate downstream checkpoint, projection,
  or readiness state and lose the separation that the architecture doc just tightened.
- Response:
  freeze the semantic root as meaning-only and make sibling artifacts explicit by
  absence in this slice.

### Edge 2: Package Timing Drift

- Risk:
  `V40-A` could activate `packages/adeu_architecture_compiler` too early and turn the
  first root slice into a partial compiler rollout.
- Response:
  keep `packages/adeu_architecture_ir` as the only active package in `vNext+77` and
  defer compiler activation to `V40-B` or later.

### Edge 3: Advisory / Authoritative Collapse

- Risk:
  world-hypothesis artifacts could be exported as if they were already authoritative
  architecture meaning.
- Response:
  freeze advisory world hypotheses as non-authoritative candidates and reserve canonical
  authority for `adeu_architecture_semantic_ir@1` only.

### Edge 4: Hash-Law Drift

- Risk:
  the slice could claim deterministic replay while schema export and fixture hashing use
  different canonicalization profiles.
- Response:
  bind schema export, root hashing, and fixture replay to one deterministic
  canonicalization profile from the start.

### Edge 5: Schema Overbreadth

- Risk:
  the first schema baseline could try to freeze too many later-family surfaces at once,
  especially conformance, hybrid, or projection artifacts.
- Response:
  activate only the five semantic-root artifacts in this arc and make the deferred
  family surfaces explicit non-goals.

### Edge 6: Formal Sidecar Authority Drift

- Risk:
  the Lean sidecar could be treated as silently authoritative over schema behavior
  before the mainline package exists.
- Response:
  keep Lean proof mirrors additive and non-blocking in this slice, with the package
  schemas and tests remaining authoritative for shipped behavior.

### Edge 7: Shape-Only Schema Baseline

- Risk:
  the first root slice could freeze only exported shells without enough root-local
  semantic discipline to catch broken refs, missing sections, or malformed ambiguity
  entries.
- Response:
  require lightweight fail-closed presence and reference-closure checks now, while
  leaving full deterministic assembly and whole-ASIR integrity to `V40-B`.

## Current Judgment

- `V40-A` is worth starting now because the repo has a stable architecture constitution
  and decomposition plan, and the semantic-root schema/export/hash baseline is the
  narrowest concrete arc that turns that design into repo-native typed substrate without
  widening prematurely into compiler or lowering work.
