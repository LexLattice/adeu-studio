# Assessment vNext+268 Edges

Status: pre-lock edge assessment for `PB-MATRIX-INCLUSION-0-C`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS268_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: C Could Register Without Released B Rows

- Risk:
  revision registration could be minted from A candidate eligibility or a
  hand-authored membership list rather than B decision records.
- Required containment:
  C must require released B amendment plan, case delta manifest,
  comparability delta review, contamination delta review, and inclusion
  decision record before revision registration validates.

### Edge 2: Revision Registration Could Add Cases Not Admitted By B

- Risk:
  revised matrix membership could include lineages that B deferred, rejected,
  or never considered.
- Required containment:
  registered included, deferred, and rejected membership sets must match B
  inclusion decision exactly.

### Edge 3: Component Hashes Could Drift Between B And Registration

- Risk:
  C could cite B refs while registering a different amendment, delta,
  comparability, contamination, decision, or membership manifest payload.
- Required containment:
  revision registration must bind base revision, amendment plan, case delta,
  comparability review, contamination review, inclusion decision, and
  membership manifest hashes.

### Edge 4: Readiness Counts Could Become Result Counts

- Risk:
  included/deferred/rejected counts could be read as pass rate, solve rate,
  success rate, benchmark score, or model performance.
- Required containment:
  readiness summary must use inventory-only and local-denominator posture and
  reject result-like or benchmark-like language.

### Edge 5: Matrix Denominator Could Become Benchmark Denominator

- Risk:
  local matrix membership count could be treated as official ProgramBench
  denominator or representative benchmark sample.
- Required containment:
  C must require `not_representative_benchmark_sample`,
  `not_benchmark_truth`, and local matrix denominator posture.

### Edge 6: Post-Inclusion Handoff Could Select Execution Or Projection

- Risk:
  handoff pressure could become direct authorization to run the revised
  matrix, project results, score benchmarks, compare baselines, or rank
  models.
- Required containment:
  handoff rows must be pressure-only, typed, and explicitly non-selecting.

### Edge 7: Family Closeout Could Overclaim The Family

- Risk:
  closeout could imply official ProgramBench readiness, result truth, or next
  family selection.
- Required containment:
  closeout must close only `PB-MATRIX-INCLUSION-0`, require exact A/B/C slice
  refs and shipped shapes, and preserve no official, benchmark-truth,
  baseline-comparison, model-ranking, or future-family authority.

## Residual Edges

- Any later result projection, batch execution, official participation,
  baseline comparison, or model comparison must be selected by a separate
  family or lock.
- The revised matrix is a local membership accounting object only until a
  later family grants execution or projection authority.

## Current Judgment

The `PB-MATRIX-INCLUSION-0-C` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=268` passes.
