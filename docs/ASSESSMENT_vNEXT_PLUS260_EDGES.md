# Assessment vNext+260 Edges

Status: pre-lock edge assessment for `PB-MATRIX-0-A`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: A Inclusion Could Bypass Released Case Lineage

- Risk:
  a matrix case could be included from a support note, loose fixture label, or
  unreleased local row instead of released `PB-TRIAL-0` and optional
  `PB-RETRY-0` lineage.
- Required containment:
  A validators must require concrete released local cleanroom lineage refs for
  every included case and fail closed on unreleased, support-only, or missing
  family closeout refs.

### Edge 2: Case Candidate Lists Could Hide Lineage Drift

- Risk:
  `included_case_refs` could become a flat list that hides mismatched adapter,
  workbench, attempt, trial, retry, or boundary refs.
- Required containment:
  inclusion manifests must use row-shaped `matrix_case_candidate_row` entries
  with explicit lineage refs, visibility boundary hash, cleanroom boundary
  hash, result-source posture, contamination posture, origin posture, and
  inclusion decision.

### Edge 3: Matrix Selection Could Look Representative

- Risk:
  a small local matrix could be described as a representative ProgramBench
  sample or benchmark-like subset.
- Required containment:
  matrix requests must carry `matrix_horizon`, `matrix_max_case_count`,
  selection rationale rows, and representativeness posture. Local smoke,
  research, regression, or coverage-probe matrices cannot claim benchmark
  representativeness.

### Edge 4: Aggregate Counts Could Become Scores

- Risk:
  included/resolved/remanded/blocked counts could be phrased as pass rate,
  solve rate, success rate, benchmark score, model score, or official success
  rate.
- Required containment:
  A rows must carry aggregate count posture as local inventory/accounting only,
  and reject benchmark-score or soft scoring language before B/C summary rows
  exist.

### Edge 5: Matrix Controls Could Become Model Comparison

- Risk:
  multiple worker/model profiles could turn the matrix into a model-comparison
  or ranking surface.
- Required containment:
  A defaults to one worker/model profile, one tool policy, one probe basis,
  and one sandbox/write-scope posture. Multi-profile matrices require
  comparability-accounting-only non-ranking posture and still cannot rank
  models.

### Edge 6: Matrix Controls Could Grant Batch Execution

- Risk:
  matrix control rows could be read as permission to run cases, execute
  commands, materialize candidates, or contact official ProgramBench surfaces.
- Required containment:
  A guardrails and control contracts must reject command execution, batch
  execution, official runner/evaluator access, source lookup, decompilation,
  internet lookup, Docker socket, host secrets, wider write scope, hidden-test
  access, official submission authority, and future-family selection.

### Edge 7: A Could Prematurely Emit B/C Artifacts

- Risk:
  A could include result projections, observation ledgers, coverage registers,
  contamination registers, matrix summaries, handoffs, or family closeout
  rows.
- Required containment:
  A fixture and bundle validation must reject `PB-MATRIX-0-B/C` artifact
  kinds. Result projection and matrix summary remain deferred.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus260/`.
- The implementation PR must run the focused `PB-MATRIX-0-A` tests and
  `make check` before opening the PR.
- Later `PB-MATRIX-0-B` must preserve projection as derived local posture, not
  new outcome truth.
- Later `PB-MATRIX-0-C` must prevent aggregate-count and summary laundering
  into benchmark score, model ranking, or official ProgramBench success.

## Current Judgment

The `PB-MATRIX-0-A` starter is bounded enough to proceed to implementation
after `make arc-start-check ARC=260` passes.
