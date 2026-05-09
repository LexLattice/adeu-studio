# Assessment vNext+265 Edges

Status: pre-lock edge assessment for `PB-CASE-EXPANSION-0-C`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS265_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: C Could Register A Case Without Complete Released A/B Lineage

- Risk:
  a local case lineage could be registered from a partial blueprint or stale
  source pool.
- Required containment:
  C must require released A and B refs, one `case_expansion_ref`, and a
  complete B blueprint, evidence pack, probe contract, oracle boundary, and
  contamination screen before lineage registration.

### Edge 2: Contaminated Blueprint Rows Could Become Registered Lineages

- Risk:
  a non-clean or inconclusive contamination screen could be treated as
  registration-ready.
- Required containment:
  lineage registration must require `contamination_status = clean` and
  `screen_verdict = passed_cleanroom_screen`; exposure refs or contamination
  blockers must fail closed.

### Edge 3: Ready Counts Could Become Benchmark-Like Scores

- Risk:
  readiness inventory counts could be read as pass rates, solve rates,
  success rates, benchmark scores, model scores, or official success rates.
- Required containment:
  readiness summaries must carry inventory-only count posture,
  expansion-request denominator posture, and non-representative benchmark
  posture. Soft scoring language must be rejected.

### Edge 4: Readiness Could Ignore Missing Probe Or Oracle Rows

- Risk:
  a case could be marked ready without complete probe contracts or oracle
  boundaries.
- Required containment:
  readiness marked ready must require complete source identity, complete
  probe contracts, complete oracle boundaries, clean contamination, and no
  carried blockers.

### Edge 5: Matrix Candidate Handoff Could Become Direct Matrix Inclusion

- Risk:
  handoff rows could be overread as adding cases to a matrix.
- Required containment:
  matrix candidate handoff must be pressure-only and non-selecting. It must
  deny direct matrix inclusion and defer all matrix accounting to a later
  matrix family or matrix update review.

### Edge 6: Handoff Could Grant Batch Execution Or Benchmark Authority

- Risk:
  a ready expanded case could trigger local execution, batch execution,
  official ProgramBench participation, benchmark scoring, or hidden evaluator
  access.
- Required containment:
  C handoff rows must reject batch execution authority, scoring authority,
  official participation, hidden evaluator access, model-ranking authority,
  retry-chain authority, and future-family selection.

### Edge 7: Family Closeout Could Omit A/B/C Surfaces

- Risk:
  the final family closeout could claim closure while omitting a slice or
  shipped shape.
- Required containment:
  family closeout alignment must list exact closed slice refs for
  `PB-CASE-EXPANSION-0-A`, `PB-CASE-EXPANSION-0-B`, and
  `PB-CASE-EXPANSION-0-C`, and must enumerate shipped A/B/C record shapes.

### Edge 8: C Could Emit Execution Or Scoring Artifacts

- Risk:
  C could ship local trial dockets, execution traces, matrix projections,
  benchmark scores, baseline comparisons, or model rankings.
- Required containment:
  C fixtures and validators must reject local execution, probe execution,
  batch execution, candidate materialization, direct matrix inclusion,
  benchmark score, baseline comparison, model ranking, official ProgramBench
  authority, hidden-test handling, and future-family selection.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus265/`.
- The implementation PR must run the focused `PB-CASE-EXPANSION-0-C` tests
  and `make check` before opening the PR.
- The family closeout produced by C must close only `PB-CASE-EXPANSION-0` and
  must not select the next ProgramBench family.

## Current Judgment

The `PB-CASE-EXPANSION-0-C` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=265` passes.
