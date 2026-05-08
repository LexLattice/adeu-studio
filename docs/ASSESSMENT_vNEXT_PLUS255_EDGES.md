# Assessment vNext+255 Edges

Status: post-closeout edge assessment for `PB-TRIAL-0-B`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS255_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Rows Could Bypass Released A Trial Law

- Closeout state:
  contained.
- Evidence:
  `validate_pb_trial_0b_execution_bundle` consumes released A trial docket,
  execution runbook, sandbox readiness review, and non-authority guardrail
  rows before the B bundle can validate.

### Edge 2: Dispatch Could Proceed Without Ready A Readiness

- Closeout state:
  contained.
- Evidence:
  validation rejects dispatch rows unless the released A sandbox readiness
  posture is `ready_for_later_local_trial_execution_review`.

### Edge 3: Dispatch Could Exist Without B-Lock Authority

- Closeout state:
  contained.
- Evidence:
  worker dispatch rows require a `dispatch_authority_ref` tied to the released
  `PB-TRIAL-0-B` lock.

### Edge 4: Multiple Dispatches Could Hide Retries

- Closeout state:
  contained.
- Evidence:
  worker dispatch rows enforce `dispatch_index = 1`; retry authority remains
  unselected and unavailable in this slice.

### Edge 5: Dispatch Could Drift From Preflighted Worker Input

- Closeout state:
  contained.
- Evidence:
  dispatch rows bind to worker input packet hash, worker-visible context hash,
  tool manifest ref, allowed and forbidden tool manifest hashes, sandbox
  instance ref, sandbox attestation bundle ref, and input packet
  materialization hash.

### Edge 6: Dispatch Could Use Hidden, Source, Internet, Or Secret Channels

- Closeout state:
  contained.
- Evidence:
  dispatch validation rejects hidden-test access, source lookup, official
  runner/evaluator contact, benchmark score, model ranking, official
  submission, and retry authority posture. The shipped reference remains local
  cleanroom only.

### Edge 7: Execution Capture Could Be Partial Or Prose-Only

- Closeout state:
  contained.
- Evidence:
  execution capture rows require transcript/stdout/stderr hashes, bounded
  excerpts, exit code, duration, timeout status, output capture policy, worker
  tool-call manifest, sandbox witness refs, and explicit local capture posture.

### Edge 8: Worker Output Could Launder Forbidden Content

- Closeout state:
  contained.
- Evidence:
  forbidden-content screening rows and verdict are required; candidate
  snapshots are blocked unless the screen verdict is `passed`.

### Edge 9: Candidate Snapshot Could Escape Released Write Scope

- Closeout state:
  contained.
- Evidence:
  candidate snapshots require the released write scope, pre/post filesystem
  manifests, fs-diff refs, snapshot manifest hash, generated file hashes, and
  `snapshot_inside_write_scope = true`.

### Edge 10: Candidate Snapshot Could Become Official Submission

- Closeout state:
  contained.
- Evidence:
  snapshot rows carry local-only no-official-submission and not-benchmark-truth
  postures; official submission and benchmark-truth postures are rejected.

### Edge 11: Lifecycle Projection Could Define New Evidence Law

- Closeout state:
  contained.
- Evidence:
  lifecycle projection maps to released `PB-ATTEMPT-0-B` lifecycle refs and
  requires `new_evidence_law_posture =
  no_new_evidence_law_defined_by_pb_trial_0b`.

### Edge 12: Lifecycle Projection Could Point At Stale Attempt Rows

- Closeout state:
  contained after review fix.
- Evidence:
  review feedback added released `PB-ATTEMPT-0-B` row inputs to the validator
  and a regression rejecting stale mapped attempt refs.

### Edge 13: B Could Prematurely Emit C Artifacts

- Closeout state:
  contained.
- Evidence:
  B emits only worker dispatch record, execution capture, candidate artifact
  snapshot, and lifecycle projection shapes. Outcome audit, observation
  summary, remand decision, and family closeout remain deferred to
  `PB-TRIAL-0-C`.

## Residual Edges

- `PB-TRIAL-0-C` must consume released `PB-TRIAL-0-A/B` refs before outcome
  audit, observation summary, remand decision, or family closeout can occur.
- `PB-TRIAL-0-C` must keep local acceptance scoped to declared local trial
  evidence, not hidden tests or official benchmark results.
- `PB-TRIAL-0-C` must ensure observation summaries remain single-trial-only
  and non-comparative.
- `PB-TRIAL-0-C` must ensure remand decisions carry local pressure only and
  cannot grant retry dispatch authority.
- Official ProgramBench participation, hidden evaluator integration,
  benchmark scoring, model ranking, official submissions, broader benchmark
  result governance, product, graph, release, or recursive-policy work remain
  unselected.

## Current Judgment

- `PB-TRIAL-0-B` is complete on `main`.
- The slice successfully made one local cleanroom trial specimen recordable
  without converting it into outcome acceptance, benchmark truth, official
  ProgramBench authority, model ranking, retry authority, remand authority, or
  future-family selection.
- The next valid slice is `PB-TRIAL-0-C`, under a separate starter lock.
