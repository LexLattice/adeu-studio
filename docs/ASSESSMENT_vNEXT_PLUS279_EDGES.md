# Assessment vNext+279 Edges

Status: post-closeout assessment for `BRL-0-B`.

Authority layer: closeout evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS279_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Post-Implementation Edge Review

### Edge 1: Replay Execution Becomes Probe Generation

Status: contained.

`BRL-0-B` executes only manifest-declared probe contracts. It does not invent
argv, env, cwd, stdin, fixture, timeout, cleanup, or protected surface behavior.

### Edge 2: Replay Failure Becomes Expected Hash Update

Status: contained.

Changed actual observations become structured diffs. Expected observation
hashes and suite-root baselines remain locked inputs rather than mutable repair
targets.

### Edge 3: Canonicalization Hides Protected Behavior

Status: contained.

Observation records keep raw exit, stdout, stderr, file-tree, process-state,
and timeout surfaces distinct from canonical hashes. Changed protected surfaces
are preserved in regression diff rows.

### Edge 4: Candidate Artifact Identity Is Under-Specified

Status: contained.

Replay execution reports bind candidate artifact identity and execution
environment identity before replay output can be interpreted.

### Edge 5: Diff Report Becomes Patch Authority

Status: contained.

Regression diffs are report-only. They do not recommend patches, dispatch
workers, claim product correctness, or authorize official readiness.

### Edge 6: Suite Root Report Becomes No-Regression Certificate

Status: contained.

Suite-root hash reports may say whether expected and actual suite roots match.
No-regression certificate posture remains deferred to `BRL-0-C`.

### Edge 7: B Leaks Into C

Status: contained.

Impact-cone sentinel selection, bounded no-regression certificates, stale-lock
invalidation, and HOB/OTB integration handoff remain outside `BRL-0-B`.

## Residual Risk

The residual risk is deliberately deferred rather than unsolved:

- `BRL-0-B` can report diffs but cannot decide which sentinels are sufficient
  for a touched owner surface.
- `BRL-0-B` can compute suite-root match status but cannot turn it into a
  no-regression certificate.
- `BRL-0-B` can preserve replay evidence but cannot decide whether stale owner
  maps, fixtures, artifacts, or HOB/OTB handoffs require lock refresh.

These are the selected `BRL-0-C` responsibilities.
