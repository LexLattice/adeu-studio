# Assessment vNext+259 Edges

Status: pre-lock edge assessment for `PB-RETRY-0-C`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS259_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: C Audit Could Bypass Released A/B Retry Law

- Risk:
  outcome audit could summarize a retry without consuming released retry
  request, eligibility, scope, dispatch, execution, delta snapshot, lifecycle
  projection, and sandbox trace rows.
- Required containment:
  C validators must require released `PB-RETRY-0-A` and `PB-RETRY-0-B` refs
  before outcome audit, delta summary, remand settlement, or family closeout
  rows validate.

### Edge 2: Same-Lineage Delta Could Become Cross-Attempt Comparison

- Risk:
  delta observation summaries could compare unrelated attempts, workers,
  models, tasks, official scores, hidden-test outcomes, or retry chains.
- Required containment:
  C validators must require the same retry lineage, trial lineage, cleanroom
  case lineage, worker-visible boundary, declared local probe basis, and
  local-only benchmark-not-truth posture.

### Edge 3: Local Retry Resolution Could Hide Evidence Gaps

- Risk:
  `local_retry_resolved` could be emitted while contamination, sandbox
  violation, output capture gaps, candidate delta gaps, lifecycle projection
  gaps, or remand satisfaction gaps remain.
- Required containment:
  local retry resolution must fail closed unless all required local-only
  evidence and remand satisfaction rows are present and clean.

### Edge 4: Delta Summary Could Become Model Or Benchmark Ranking

- Risk:
  same-lineage observations could use soft ranking language such as "model B
  is better", "this approach wins", "benchmark-like result", or "near
  leaderboard".
- Required containment:
  C validators and reject fixtures must block model-ranking,
  benchmark-ranking, leaderboard, official-score, hidden-test, cross-task,
  cross-worker, and unrelated-attempt comparison claims.

### Edge 5: Remand Settlement Could Become Second Retry Authority

- Risk:
  unresolved or new local remand refs could be treated as retry eligibility,
  dispatch authority, or an automatic second retry request.
- Required containment:
  remand settlement must require `second_retry_requestability_posture =
  no_second_retry_authority_granted_by_pb_retry_0c` and must preserve new
  remand refs as pressure only.

### Edge 6: Settlement Could Cite Forbidden Evidence

- Risk:
  remand settlement could cite hidden-test failure, official evaluator
  feedback, original source facts, decompilation facts, internet lookup facts,
  or external repository facts.
- Required containment:
  C validators must allow only local cleanroom retry evidence and reject
  forbidden evidence categories, including derived summaries.

### Edge 7: Family Closeout Could Select The Next Family

- Risk:
  closeout alignment could turn `PB-RETRY-0` settlement into official
  ProgramBench participation, second retry selection, or another future-family
  selection.
- Required containment:
  family closeout alignment must close exactly `PB-RETRY-0-A/B/C` and require
  `future_family_authority_posture` to deny future-family selection.

## Residual Edges

- The implementation PR must add focused reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus259/`.
- The implementation PR must run the focused `PB-RETRY-0-C` tests and
  `make check` before opening the PR.
- Final family closeout after merge must replace this scaffold with
  post-closeout evidence and deterministic stop-gate artifacts.

## Current Judgment

The `PB-RETRY-0-C` starter is bounded enough to proceed to implementation
after `make arc-start-check ARC=259` passes.
