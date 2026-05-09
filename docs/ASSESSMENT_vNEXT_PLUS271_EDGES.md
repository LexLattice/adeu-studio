# Assessment vNext+271 Edges

Status: pre-lock edge assessment for `PB-SINGLE-CASE-RUN-0-C`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS271_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: C Could Audit Without Released A/B Lineage

- Risk:
  outcome rows could be authored without the released target-selection,
  preflight, dispatch, trace, probe, capture, and projection evidence.
- Required containment:
  C must require released A and B refs before local outcome audit validates.

### Edge 2: Local Acceptance Could Hide Missing Probe Evidence

- Risk:
  the local specimen could be accepted despite missing positive or negative
  probe observations.
- Required containment:
  local acceptance requires all required positive probes to pass and all
  required negative probes to pass or be explicitly not applicable with reason.

### Edge 3: Unsafe Candidate Artifacts Could Be Accepted

- Risk:
  output could be treated as accepted even when artifact capture is missing,
  outside write scope, or not safely screened.
- Required containment:
  local acceptance requires candidate artifact capture to exist, stay inside
  released write scope, pass forbidden-content screening, and bind artifact
  hashes consistently.

### Edge 4: Lifecycle Projection Gaps Could Be Ignored

- Risk:
  a local outcome could be accepted without a valid projection into released
  attempt/trial/workbench vocabulary.
- Required containment:
  C acceptance must block on lifecycle projection gaps and require released
  validator bindings.

### Edge 5: Observation Summary Could Become Benchmark Language

- Risk:
  local observations could be summarized as ProgramBench pass/fail, score,
  success rate, baseline win, model improvement, representative result, or
  hidden-test equivalence.
- Required containment:
  observation summaries must carry a local-only scope statement and reject soft
  benchmark, baseline, ranking, leaderboard, official-like, and hidden-test
  language.

### Edge 6: Remand Pressure Could Become Retry Authority

- Risk:
  a remand decision could be read as permission to run a retry.
- Required containment:
  remand decisions must state pressure-only posture and
  `no_retry_authority_granted_by_pb_single_case_run_0c`.

### Edge 7: Handoff Or Closeout Could Select The Next Family

- Risk:
  family closeout or handoff rows could grant official participation, batch
  execution, benchmark-result governance, retry governance, or future-family
  selection.
- Required containment:
  handoff rows must be pressure-only and non-selecting; family closeout may
  close only `PB-SINGLE-CASE-RUN-0`.

## Residual Edges

- Official ProgramBench runner/evaluator integration remains unselected.
- Hidden-test handling and hidden-test equivalence remain unselected.
- Benchmark scoring, baseline comparison, and model ranking remain unselected.
- Batch execution over a matrix remains unselected.
- Retry authority remains unselected.
- Future-family selection remains unselected by this starter.

## Current Judgment

The `PB-SINGLE-CASE-RUN-0-C` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=271` passes. It audits one
captured local specimen and closes this family without creating new execution,
retry, official benchmark, scoring, ranking, or future-family authority.
