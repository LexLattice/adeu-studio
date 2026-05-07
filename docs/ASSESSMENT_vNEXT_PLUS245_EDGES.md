# Assessment vNext+245 Edges

Status: pre-lock edge assessment for `PB-ADAPTER-0-A`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS245_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Task Intake Could Become Task Solving

- Pre-lock judgment: `guarded_by_scope`.
- Planned control:
  `PB-ADAPTER-0-A` emits task intake, artifact manifest, visibility manifest,
  worker access contract, and guardrail rows only.
- Residual:
  probe observation, reconstruction execution, generated submissions, and
  official ProgramBench participation remain deferred.

### Edge 2: Artifact Identity Could Drift

- Pre-lock judgment: `requires_hash_manifest`.
- Planned control:
  `programbench_task_artifact_manifest@1` must bind reference executable,
  usage docs, visible input artifacts, source-set hash, observed-at or
  snapshot refs, origin posture, and ingestion method.
- Residual:
  later probe observations and case packets must consume the same released
  artifact identity rather than reassembling a different task surface.

### Edge 3: Hidden Or Forbidden Evidence Could Be Exposed

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  hidden and forbidden rows cannot appear in worker-visible refs, allowed
  inference refs, or cleanroom-visible derived summaries.
- Residual:
  postmortem-only and hidden-evaluator material may be represented only as
  non-inference posture unless a later family selects stronger governance.

### Edge 4: Derived Summary Could Launder Forbidden Evidence

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  derived summary policy rows inherit the strictest source visibility and
  reject summaries of hidden or forbidden material as worker evidence.
- Residual:
  review should inspect fixture rejects for hidden/forbidden advisory text
  marked cleanroom-visible.

### Edge 5: Worker Access Contract Could Grant Execution Too Early

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  slice A requires no command execution authority, no probe execution
  authority, and no submission generation authority.
- Residual:
  `PB-ADAPTER-0-B` may later represent probe plans and observations only under
  a separate lock.

### Edge 6: Public Descriptor Could Become Benchmark Truth

- Pre-lock judgment: `guarded_context_only`.
- Planned control:
  public descriptors and ProgramBench-style labels remain context-only and
  cannot become task truth, benchmark truth, hidden-test evidence, scores, or
  rankings.
- Residual:
  official ProgramBench participation and benchmark-result governance remain
  unselected.

### Edge 7: Slice A Could Include B/C Artifacts

- Pre-lock judgment: `must_reject_future_slice_artifacts`.
- Planned control:
  validators and reject fixtures should fail on probe observation rows,
  reconstruction case packets, readiness summaries, handoffs, and family
  closeout alignment in slice A.
- Residual:
  B and C remain mapped but unimplemented.

## Current Judgment

- `PB-ADAPTER-0-A` is a coherent first slice after `PB-PY-0`.
- The starter should proceed to external review as a docs-only lock bundle.
- Implementation should wait until this main family bundle and slice-A starter
  bundle are accepted.
