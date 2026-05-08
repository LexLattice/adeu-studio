# Assessment vNext+256 Edges

Status: pre-lock edge assessment for `PB-TRIAL-0-C`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS256_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: C Rows Could Bypass Released A/B Trial Law

- Planned containment:
  outcome audit, observation summary, remand decision, and family closeout
  rows must bind to released A docket/runbook/readiness/guardrail refs and
  released B dispatch/capture/snapshot/projection refs.
- Required implementation evidence:
  reject missing, stale, or mismatched A/B refs.

### Edge 2: Outcome Audit Could Claim Official Benchmark Truth

- Planned containment:
  outcome audit rows carry explicit no-hidden-test-equivalence,
  not-benchmark-truth, no-model-ranking, and no-official-submission postures.
- Required implementation evidence:
  reject hidden-test equivalence, benchmark truth, official evaluator truth,
  model ranking, official submission, or official ProgramBench authority.

### Edge 3: Local Acceptance Could Ignore Missing Evidence

- Planned containment:
  `trial_locally_accepted` requires no carried blockers, no sandbox violation,
  no lifecycle projection gap, no output capture gap, a candidate snapshot
  inside released write scope, and lifecycle projection validation against
  released `PB-ATTEMPT-0` bindings.
- Required implementation evidence:
  reject local acceptance with blockers, missing snapshot, outside-write-scope
  snapshot, output capture gap, or missing lifecycle projection validation.

### Edge 4: Observation Summary Could Become A Model Ranking

- Planned containment:
  observation summaries are single-trial-only, non-comparative, and not
  benchmark-score or leaderboard rows.
- Required implementation evidence:
  reject comparative language across models, attempts, retries, benchmark rows,
  or leaderboard posture.

### Edge 5: Observation Summary Could Overstate Scope

- Planned containment:
  summaries report only the one local trial specimen and its local evidence.
- Required implementation evidence:
  reject summary rows that claim official task success, hidden-test
  equivalence, ProgramBench resolution, benchmark score, or generalized model
  performance.

### Edge 6: Remand Decision Could Cite Forbidden Sources

- Planned containment:
  remand source kinds are local only: execution capture gap, candidate snapshot
  gap, lifecycle projection gap, sandbox readiness/application gap,
  worker-declared uncertainty, runbook satisfaction gap, or local evidence
  inconclusive.
- Required implementation evidence:
  reject hidden-test failure, official evaluator feedback, original-source
  fact, decompilation fact, internet lookup fact, or external-repo fact.

### Edge 7: Remand Decision Could Become Retry Authority

- Planned containment:
  remand rows may carry local pressure only and must carry explicit no-retry
  authority posture.
- Required implementation evidence:
  reject retry dispatch authority, worker redispatch authority, or next-attempt
  selection posture.

### Edge 8: Family Closeout Could Select The Next Family

- Planned containment:
  family closeout closes only `PB-TRIAL-0-A`, `PB-TRIAL-0-B`, and
  `PB-TRIAL-0-C`; it may not select official ProgramBench participation,
  retry/multi-attempt work, benchmark governance, product, graph, release,
  recursive-policy work, or future-family selection.
- Required implementation evidence:
  reject future-family selection or out-of-family closeout claims.

### Edge 9: C Could Emit Execution Or Candidate Mutation Artifacts

- Planned containment:
  C is an audit/summary/remand/closeout slice only; dispatch, execution
  capture, candidate materialization, candidate snapshot mutation, and probe
  execution remain outside C.
- Required implementation evidence:
  reject new dispatch, run trace, candidate materialization, or command
  execution artifacts in C fixtures.

## Residual Edges

- The next ProgramBench practical arc, if any, must be selected only after
  `PB-TRIAL-0-C` closes and must not be inferred from this starter.
- Retry dispatch authority, multi-attempt comparison, official ProgramBench
  participation, hidden evaluator integration, benchmark scoring, model
  ranking, official submissions, broader benchmark result governance, product,
  graph, release, or recursive-policy work remain unselected.

## Current Judgment

- `PB-TRIAL-0-C` is ready as a bounded starter candidate.
- The slice can audit and close one local cleanroom trial, but it cannot grant
  official ProgramBench authority, hidden-test equivalence, benchmark truth,
  retry authority, model ranking, official submission authority, or
  future-family selection.
