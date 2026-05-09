# Assessment vNext+262 Edges

Status: pre-lock edge assessment for `PB-MATRIX-0-C`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS262_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: C Summary Could Ignore Released A/B Basis

- Risk:
  a matrix summary could cite cases or outcomes not admitted by released
  `PB-MATRIX-0-A` or projected by released `PB-MATRIX-0-B`.
- Required containment:
  C validators must consume released A request/inclusion/eligibility/control/
  guardrail rows and released B projection/observation/coverage/contamination
  rows before summary, handoff, or closeout rows validate.

### Edge 2: Local Complete Could Hide Gaps Or Blockers

- Risk:
  summary could mark a matrix complete while projection gaps, contamination
  blockers, missing coverage, or unresolved blockers remain.
- Required containment:
  local complete posture must require no projection gaps, clean contamination,
  no missing local coverage, and no unresolved carried blockers.

### Edge 3: Aggregate Counts Could Become Benchmark Score

- Risk:
  local case counts could be read as pass rate, solve rate, success rate,
  benchmark score, official success rate, model score, or leaderboard metric.
- Required containment:
  summary rows must carry aggregate-count posture, representativeness posture,
  matrix scope statement, not-benchmark-score statement, and validators that
  reject scoring/ranking language.

### Edge 4: Summary Could Claim Official ProgramBench Or Hidden-Test Truth

- Risk:
  local matrix summary could imply hidden-test equivalence, official evaluator
  success, official submission readiness, or benchmark truth.
- Required containment:
  benchmark truth posture must remain `not_benchmark_truth`, hidden-test
  equivalence must remain absent, and official ProgramBench participation
  authority must be rejected.

### Edge 5: Handoff Could Become Authority

- Risk:
  post-matrix handoff pressure could be overread as authority to run more
  cases, contact official evaluators, compare models, execute batches, or
  select the next family.
- Required containment:
  handoff rows must be pressure-only, typed, non-selecting, and explicitly
  deny official participation, hidden evaluator access, model-ranking
  authority, batch execution authority, retry-chain authority, and
  future-family selection.

### Edge 6: Family Closeout Could Omit A Slice

- Risk:
  family closeout alignment could close `PB-MATRIX-0` without proving A, B,
  and C rows shipped and align.
- Required containment:
  closeout alignment must list A/B/C closed slice refs, all shipped record
  shapes, summary refs, handoff refs, and future-family non-authority posture.

### Edge 7: C Could Become Execution Or Batch Surface

- Risk:
  summary or closeout rows could introduce execution, command, batch,
  materialization, official runner, or official evaluator surfaces.
- Required containment:
  C fixtures and validators must reject execution records, batch authority,
  candidate materialization, official runner/evaluator integration, hidden-test
  handling, official submission authority, and retry-chain authority.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus262/`.
- The implementation PR must run the focused `PB-MATRIX-0-C` tests and
  `make check` before opening the PR.
- The final family closeout after C merge must close the entire `PB-MATRIX-0`
  arc without selecting the next family.

## Current Judgment

The `PB-MATRIX-0-C` starter is bounded enough to proceed to implementation
after `make arc-start-check ARC=262` passes.
