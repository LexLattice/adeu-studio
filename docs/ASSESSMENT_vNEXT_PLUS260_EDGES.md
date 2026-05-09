# Assessment vNext+260 Edges

Status: post-closeout edge assessment for `PB-MATRIX-0-A`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: A Inclusion Could Bypass Released Case Lineage

- Closeout state:
  contained.
- Evidence:
  bundle validation consumes released local cleanroom lineage refs and
  rejects unreleased, support-only, contaminated, hidden-test-derived,
  evaluator-derived, source-lookup-derived, decompilation-derived,
  internet-derived, external-repo-derived, and postmortem-only included cases.

### Edge 2: Case Candidate Lists Could Hide Lineage Drift

- Closeout state:
  contained.
- Evidence:
  inclusion manifests require row-shaped case candidates with explicit
  adapter, workbench, attempt, trial, optional retry, visibility-boundary,
  cleanroom-boundary, result-source, contamination, origin, inclusion
  decision, and inclusion reason fields.

### Edge 3: Candidate Eligibility Could Be Checked Only For Included Cases

- Closeout state:
  contained after review fix.
- Evidence:
  bundle validation now requires lineage eligibility rows to cover every
  manifest case candidate, including blocked, deferred, and support-only
  candidates.

### Edge 4: Matrix Selection Could Look Representative

- Closeout state:
  contained.
- Evidence:
  matrix requests require `matrix_horizon`, `matrix_max_case_count`,
  selection rationale rows, and `not_representative_benchmark_sample`
  posture where applicable. Representative benchmark subset claims are
  rejected.

### Edge 5: Aggregate Counts Could Become Scores

- Closeout state:
  contained.
- Evidence:
  request and control rows carry local inventory/accounting aggregate-count
  posture, and validators reject benchmark score, pass rate, solve rate,
  success rate, official-like score, leaderboard, model superiority, and
  model-ranking language.

### Edge 6: Matrix Controls Could Become Model Comparison

- Closeout state:
  contained after review fix.
- Evidence:
  multi-profile or multi-control matrices require both profile-level and
  matrix-level comparability-accounting-only posture, and still cannot rank
  models.

### Edge 7: Matrix Controls Could Grant Batch Execution

- Closeout state:
  contained.
- Evidence:
  control contracts and guardrails reject command execution, batch execution,
  official runner/evaluator access, source lookup, decompilation, internet
  lookup, Docker socket, host secrets, wider write scope, hidden-test access,
  second retry authority, retry-chain authority, and future-family selection.

### Edge 8: Duplicate Action Or Authority Rows Could Mask Drift

- Closeout state:
  contained after review fix.
- Evidence:
  validators reject duplicate `action_kind` rows in forbidden matrix actions
  and duplicate `authority_kind` rows in non-authority guardrails.

### Edge 9: A Could Prematurely Emit B/C Artifacts

- Closeout state:
  contained.
- Evidence:
  A emits only request, inclusion manifest, eligibility review, control
  contract, and non-authority guardrail shapes. Result projection,
  observation ledger, coverage register, contamination register, matrix
  summary, handoff, and family closeout remain deferred.

## Residual Edges

- `PB-MATRIX-0-B` must consume released `PB-MATRIX-0-A` rows before result
  projection, observation ledger, coverage register, or contamination
  register rows can validate.
- `PB-MATRIX-0-B` must preserve projection as derived local posture, not new
  outcome truth.
- `PB-MATRIX-0-B` must keep coverage local-only and reject hidden-test or
  official-evaluator coverage.
- `PB-MATRIX-0-C` must prevent aggregate-count and summary laundering into
  benchmark score, model ranking, official ProgramBench success, or
  leaderboard posture.

## Current Judgment

`PB-MATRIX-0-A` is closed. The next bounded slice is `PB-MATRIX-0-B`.
