# Assessment vNext+279 Edges

Status: pre-lock assessment for `BRL-0-B`.

Authority layer: planning.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS279_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Pre-Implementation Edge Review

### Edge 1: Replay Execution Becomes Probe Generation

- Required containment:
  `BRL-0-B` may execute only manifest-declared probe contracts from released
  `BRL-0-A` records. It may not invent argv, env, cwd, stdin, fixture, timeout,
  or cleanup behavior.

### Edge 2: Replay Failure Becomes Expected Hash Update

- Required containment:
  changed actual observations must become diffs. Expected observations and
  suite-root baselines must never be silently rewritten by B.

### Edge 3: Canonicalization Hides Protected Behavior

- Required containment:
  B must reuse the locked canonicalization profile and preserve A's protected
  surface constraints for exit code, stderr, timeout, file tree, and process
  state.

### Edge 4: Candidate Artifact Identity Is Under-Specified

- Required containment:
  execution reports must bind candidate artifact identity and execution
  environment identity before replay output can be interpreted.

### Edge 5: Diff Report Becomes Patch Authority

- Required containment:
  regression diffs are report-only. They may not recommend or authorize code
  patches, worker dispatch, product correctness, or official readiness.

### Edge 6: Suite Root Report Becomes No-Regression Certificate

- Required containment:
  suite-root hash reports may say whether expected and actual suite roots match.
  Certificate posture remains deferred to `BRL-0-C`.

### Edge 7: B Leaks Into C

- Required containment:
  impact-cone sentinel selection, no-regression certificates, stale-lock
  invalidation, and HOB/OTB integration handoff remain deferred.

## Implementation Watchpoints

- Preserve released A validation and hash checks instead of recomputing or
  weakening manifest validity.
- Keep raw observation material and canonical hashes distinct.
- Keep timeout, process-state, and file-tree mutation visible in diff rows.
- Include deterministic ordering tests for observation, diff, and suite-root
  rows.
