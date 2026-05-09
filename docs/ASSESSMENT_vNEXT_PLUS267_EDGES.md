# Assessment vNext+267 Edges

Status: post-closeout edge assessment for `PB-MATRIX-INCLUSION-0-B`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS267_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Could Include Candidates Not Released By A

- Closeout state:
  contained.
- Evidence:
  B bundle validation requires released A request, candidate intake,
  eligibility, control, and guardrail refs and rejects non-eligible A review
  posture.

### Edge 2: Delta Rows Could Drop Or Duplicate Candidates

- Closeout state:
  contained.
- Evidence:
  amendment plan and case delta manifest must account for every A-eligible
  candidate exactly once as added, deferred, or rejected.

### Edge 3: Inclusion Decisions Could Become Quality Judgments

- Closeout state:
  contained.
- Evidence:
  decision basis rows use governance/accounting enum values only, reject soft
  performance language, and carry explicit non-result, non-quality-score, and
  non-benchmark-selection postures.

### Edge 4: Decision Basis Could Contradict The Recorded Outcome

- Closeout state:
  contained after review hardening.
- Evidence:
  included lineages require `lineage_eligible`; deferred lineages require
  deferred basis kinds; rejected lineages require blocked basis kinds. The B
  bundle also requires decision basis kinds to match case delta reasons.

### Edge 5: Comparability Review Could Become Model Or Baseline Comparison

- Closeout state:
  contained after review hardening.
- Evidence:
  comparability review binds base/candidate worker, model, tool, probe,
  source visibility, and sandbox/write-scope hashes. `unchanged` requires
  matching hashes; changed non-comparable posture requires a hash delta. Model
  ranking and baseline comparison authority remain denied.

### Edge 6: Contamination Could Transfer Through Summaries

- Closeout state:
  contained.
- Evidence:
  contamination delta review requires category/count/reason redaction and
  rejects hidden, forbidden, postmortem-only, evaluator-derived,
  source-derived, decompilation-derived, internet-derived, and external-repo
  content markers in visible notes.

### Edge 7: B Could Prematurely Register A Matrix Revision

- Closeout state:
  contained.
- Evidence:
  B ships amendment and decision evidence only. Revision registration,
  readiness summary, post-inclusion handoff, and family closeout remain
  deferred to `PB-MATRIX-INCLUSION-0-C`.

### Edge 8: B Could Grant Execution Or Result Projection Authority

- Closeout state:
  contained.
- Evidence:
  B rows deny execution, probe execution, batch execution, candidate
  materialization, result projection, benchmark scoring, baseline comparison,
  model ranking, official ProgramBench authority, and future-family
  selection.

## Residual Edges

- `PB-MATRIX-INCLUSION-0-C` must consume released B rows before registering
  any local matrix revision.
- C must bind revision registration to B hashes and membership decisions.
- C must keep revision readiness counts inventory-only and matrix denominator
  posture local-only, not benchmark denominator or score posture.
- C post-inclusion handoff rows must remain pressure-only and non-selecting.
- Any later result projection or batch execution must be governed by a
  separate selected family or lock.

## Current Judgment

`PB-MATRIX-INCLUSION-0-B` is closed as an amendment and inclusion-decision
seam only. The `PB-MATRIX-INCLUSION-0` family remains open for
`PB-MATRIX-INCLUSION-0-C`.
