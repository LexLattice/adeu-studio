# Assessment vNext+267 Edges

Status: pre-lock edge assessment for `PB-MATRIX-INCLUSION-0-B`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS267_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Could Include Candidates Not Released By A

- Risk:
  amendment rows could add cases that A never marked eligible.
- Required containment:
  B must require released A refs and reject A-blocked, A-deferred, or
  A-unknown candidates.

### Edge 2: Delta Rows Could Drop Or Duplicate Candidates

- Risk:
  the case delta manifest could omit an eligible candidate or list one
  candidate more than once.
- Required containment:
  delta rows must account for every A-eligible candidate exactly once as
  added, deferred, or rejected.

### Edge 3: Inclusion Decisions Could Become Quality Judgments

- Risk:
  `added`, `deferred`, or `rejected` could be read as likely pass/fail,
  score, model advantage, or benchmark relevance.
- Required containment:
  decision basis rows must use governance/accounting reasons only, with
  explicit result, quality-score, and benchmark-selection non-authority
  postures.

### Edge 4: Comparability Review Could Become Model Or Baseline Comparison

- Risk:
  hash-pair continuity checks could be read as permission to compare models,
  workers, baselines, or profiles.
- Required containment:
  comparability review must bind base/candidate worker, model, tool, probe,
  source visibility, and sandbox/write-scope hashes while requiring
  local-accounting-only non-comparison posture.

### Edge 5: Contamination Could Transfer Through Summaries

- Risk:
  hidden, forbidden, source-derived, or evaluator-derived material could leak
  through labels, rationale rows, decision rows, or redacted summaries.
- Required containment:
  contamination delta review must enforce category/count/reason redaction and
  reject content-bearing hidden or forbidden detail.

### Edge 6: B Could Prematurely Register A Matrix Revision

- Risk:
  amendment and inclusion decision rows could be treated as a revised matrix
  membership registration.
- Required containment:
  revision registration, readiness summary, post-inclusion handoff, and
  family closeout remain deferred to `PB-MATRIX-INCLUSION-0-C`.

### Edge 7: B Could Grant Execution Or Result Projection Authority

- Risk:
  inclusion decisions could be interpreted as permission to run cases or
  project results.
- Required containment:
  B must preserve no execution, no probe execution, no batch execution, no
  candidate materialization, no result projection, and no benchmark scoring
  authority.

### Edge 8: B Could Select The Next Family

- Risk:
  a completed inclusion decision could become direct handoff into C, result
  projection, batch execution, or benchmark governance.
- Required containment:
  B may create only local amendment/decision evidence; future-family
  selection remains absent.

## Residual Edges

- `PB-MATRIX-INCLUSION-0-C` must consume released B rows before registering
  any local matrix revision.
- C must keep revision counts inventory-only and matrix denominator posture
  local-only, not benchmark denominator or score posture.
- Any later result projection or batch execution must be governed by a
  separate selected family or lock.

## Current Judgment

The `PB-MATRIX-INCLUSION-0-B` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=267` passes.
