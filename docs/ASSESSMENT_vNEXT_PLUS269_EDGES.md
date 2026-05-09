# Assessment vNext+269 Edges

Status: post-closeout edge assessment for `PB-SINGLE-CASE-RUN-0-A`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS269_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edges

### Edge 1: Slice A Could Become A Second Trial Surface

- Outcome:
  `pass`.
- Evidence:
  A records single-case run relation to prior lifecycle and consumes matrix
  inclusion C lineage as target-selection substrate. It does not duplicate
  `PB-TRIAL-0` execution semantics.

### Edge 2: Target Origin Could Be Under-Specified

- Outcome:
  `pass`.
- Evidence:
  A requires `target_origin_route`, route-specific posture, required refs, and
  matrix revision identity for the default `matrix_member` route.

### Edge 3: Deferred Or Rejected Matrix Candidates Could Be Run

- Outcome:
  `pass`.
- Evidence:
  target selection requires `matrix_membership_status = included`; bundle
  validation also rejects blocked target selections and blocker refs.

### Edge 4: Direct Adapter Intake Could Bypass Matrix Governance

- Outcome:
  `pass`.
- Evidence:
  the default reference path is matrix-member only; non-matrix routes require
  explicit exception posture and are not the accepted bundle path.

### Edge 5: Preflight Could Be Misread As Dispatch Authority

- Outcome:
  `pass`.
- Evidence:
  preflight requires `preflight_scope_posture =
  eligibility_review_only_no_dispatch` and
  `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_single_case_run_0a`.

### Edge 6: B Witnesses Could Be Claimed In A

- Outcome:
  `pass`.
- Evidence:
  A records required B witness refs only. It does not record a sandbox
  instance, sandbox attestation bundle, network witness, Docker socket witness,
  secret witness, source lookup witness, decompilation witness, or write-scope
  attestation.

### Edge 7: Single Case Run Could Become Single Benchmark Result

- Outcome:
  `pass`.
- Evidence:
  A rejects benchmark-like result language and grants no benchmark truth,
  benchmark score, pass-rate, solve-rate, success-rate, baseline comparison,
  model ranking, leaderboard, official participation, hidden-test equivalence,
  or official submission authority.

## Review Feedback Integrated

- Codex review:
  - ready preflight now requires the full required check-kind set and rejects
    duplicate check kinds;
  - bundle validation rejects target selections that are blocked or carry
    blocker refs.
- Gemini review:
  - required B witness refs are immutable in module scope while payloads remain
    sorted-list validated;
  - bundle hash comparisons were expanded from dynamic `getattr` loops to
    explicit field comparisons for auditability.

## Residual Edges

- Actual worker dispatch and local execution remain deferred to
  `PB-SINGLE-CASE-RUN-0-B`.
- Local probe observation, candidate artifact capture, and lifecycle
  projection remain deferred to `PB-SINGLE-CASE-RUN-0-B`.
- Local outcome audit, observation summary, remand/acceptance decision, and
  handoff remain deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Official ProgramBench runner/evaluator integration remains unselected.
- Hidden-test handling and hidden-test equivalence remain unselected.
- Benchmark scoring, baseline comparison, and model ranking remain unselected.
- Batch execution over a matrix remains unselected.
- Future-family selection remains unselected by this slice.

## Current Judgment

`PB-SINGLE-CASE-RUN-0-A` is closed on `main` as preflight-only single-case
target selection. The next selected seam may be `PB-SINGLE-CASE-RUN-0-B`,
which is action-adjacent and must require explicit B-slice dispatch authority
before any local specimen record is accepted.
