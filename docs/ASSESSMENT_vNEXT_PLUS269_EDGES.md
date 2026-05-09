# Assessment vNext+269 Edges

Status: pre-lock edge assessment for `PB-SINGLE-CASE-RUN-0-A`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS269_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Slice A Could Become A Second Trial Surface

- Risk:
  `PB-SINGLE-CASE-RUN-0-A` could duplicate `PB-TRIAL-0-A` semantics instead
  of acting as a selected case-lineage run wrapper.
- Required containment:
  A must record `single_case_run_relation_to_prior_lifecycle` and bind the
  selected target to released adapter, workbench, attempt, trial, optional
  retry, case-expansion, matrix, or matrix-inclusion lineage as constraints.

### Edge 2: Target Origin Could Be Under-Specified

- Risk:
  a run request could cite a case lineage without saying whether it came from
  matrix membership, expanded case readiness, or direct adapter exception.
- Required containment:
  A must require `target_origin_route`, route-specific required refs, and
  route-specific validation.

### Edge 3: Deferred Or Rejected Matrix Candidates Could Be Run

- Risk:
  a case seen during matrix inclusion could be selected even though it was
  deferred or rejected rather than included.
- Required containment:
  matrix-origin targets must bind source matrix revision identity and
  `matrix_membership_status = included`.

### Edge 4: Direct Adapter Intake Could Bypass Matrix Governance

- Risk:
  direct adapter case selection could become the normal path, bypassing the
  matrix/case-lineage governance that motivated this family.
- Required containment:
  `direct_adapter_case_exception` requires explicit exception posture and
  non-matrix-lineage warning.

### Edge 5: Preflight Could Be Misread As Dispatch Authority

- Risk:
  a ready preflight packet could be treated as permission to run a worker.
- Required containment:
  A must require `preflight_scope_posture =
  eligibility_review_only_no_dispatch` and
  `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_single_case_run_0a`.

### Edge 6: B Witnesses Could Be Claimed In A

- Risk:
  A could appear to prove sandbox instance, network, Docker socket, secret,
  source lookup, decompilation, or write-scope attestations before execution.
- Required containment:
  A may list `required_b_witness_refs`, but those witnesses remain deferred
  for B.

### Edge 7: Single Case Run Could Become Single Benchmark Result

- Risk:
  a local run target could be framed as ProgramBench pass/fail truth,
  benchmark score, baseline comparison, or model performance.
- Required containment:
  A guardrail must reject benchmark score, pass-rate, solve-rate,
  success-rate, baseline, model-ranking, leaderboard, official participation,
  and hidden-test-equivalence authority.

## Residual Edges

- Actual worker dispatch and local execution remain deferred to
  `PB-SINGLE-CASE-RUN-0-B`.
- Local outcome audit, remand/acceptance decision, and handoff remain
  deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Official ProgramBench runner/evaluator integration remains unselected.
- Hidden-test handling and hidden-test equivalence remain unselected.
- Benchmark scoring, baseline comparison, and model ranking remain unselected.
- Batch execution over a matrix remains unselected.
- Future-family selection remains unselected by this starter.

## Current Judgment

The `PB-SINGLE-CASE-RUN-0-A` starter is bounded enough to proceed to
implementation after `make arc-start-check ARC=269` passes.
