# Assessment vNext+254 Edges

Status: pre-lock edge assessment for `PB-TRIAL-0-A`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS254_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: A Rows Could Bypass Released `PB-ATTEMPT-0` Lifecycle Law

- Planned containment:
  trial docket, runbook, readiness review, and guardrail rows must bind to
  released `PB-ATTEMPT-0` request/input/preflight/guardrail/result-review
  context and family closeout refs before validation succeeds.
- Required implementation evidence:
  reject missing or mismatched attempt lifecycle refs.

### Edge 2: Prior Attempt Result Review Could Be Mistaken For Trial Outcome

- Planned containment:
  `prior_attempt_result_review_context_ref` is lifecycle / closeout /
  eligibility context only. It must not count as `PB-TRIAL-0` outcome
  evidence.
- Required implementation evidence:
  reject a trial docket or runbook that treats prior result review as this
  trial's outcome.

### Edge 3: Trial Docket Could Select Multiple Attempts

- Planned containment:
  trial cardinality is `single_trial_only`, with exactly one attempt request,
  one worker input packet, one dispatch preflight, and one attempt guardrail.
- Required implementation evidence:
  reject multiple attempt request refs in one docket.

### Edge 4: Runbook Could Become Dispatch Or Command Authority

- Planned containment:
  runbook scope posture is execution-plan-only; dispatch and execution
  authority postures are explicit negatives.
- Required implementation evidence:
  reject runbook rows that grant worker dispatch or command execution.

### Edge 5: Runbook Could Be Non-Replayable

- Planned containment:
  runbook requires worker input packet hash, worker-visible context hash,
  runbook hash, input materialization policy ref, sandbox/budget refs, and
  sandbox witness requirement refs.
- Required implementation evidence:
  reject missing hash or materialization-policy fields.

### Edge 6: Sandbox Readiness Could Be Prose-Only

- Planned containment:
  readiness rows must cover network disabled, source lookup disabled,
  decompilation disabled, Docker socket absent, host secrets absent, bounded
  write scope, closed tool manifest, and run budget.
- Required implementation evidence:
  reject readiness marked ready with incomplete readiness rows.

### Edge 7: Readiness Could Pass Without Later Witness Requirements

- Planned containment:
  readiness marked ready requires every readiness check row to map to a later
  B sandbox witness requirement ref.
- Required implementation evidence:
  reject ready rows missing witness requirement refs.

### Edge 8: Tool Manifest Could Remain Open

- Planned containment:
  readiness marked ready requires closed tool manifest posture.
- Required implementation evidence:
  reject readiness marked ready with non-closed tool manifest posture.

### Edge 9: Trial Guardrail Could Miss Official Or Benchmark Authority

- Planned containment:
  guardrail rows reject official ProgramBench participation, hidden-test
  inference, source lookup, official submission, benchmark truth, model
  ranking, retry authority, and future-family selection.
- Required implementation evidence:
  reject any positive official benchmark, score, ranking, submission, retry,
  or future-family posture.

### Edge 10: Slice A Could Prematurely Emit B/C Artifacts

- Planned containment:
  A emits only docket, runbook, readiness review, and non-authority guardrail
  shapes.
- Required implementation evidence:
  reject worker dispatch, execution capture, candidate snapshot, lifecycle
  projection, outcome audit, observation summary, remand decision, and family
  closeout artifacts in A fixtures.

## Residual Edges

- `PB-TRIAL-0-A` closes only the non-executing docket/runbook/readiness seam.
- `PB-TRIAL-0-B` remains the actual execution-adjacent slice and will require
  a separate execution safety lock.
- Retry dispatch authority and multi-attempt comparison remain unselected.
- Official ProgramBench participation, hidden evaluator integration,
  benchmark scoring, model ranking, official submissions, and benchmark-result
  governance remain unselected.

## Current Judgment

- `PB-TRIAL-0-A` is ready as a bounded starter candidate.
- The slice can make one later local trial reviewable, but it cannot run it.
- The critical start-edge is explicit: prior attempt result review is context
  only; the new trial outcome cannot exist before B/C evidence exists.

