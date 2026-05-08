# Assessment vNext+257 Edges

Status: pre-lock edge assessment for `PB-RETRY-0-A`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS257_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Remand Pressure Could Become Retry Dispatch Authority

- Planned containment:
  retry request, eligibility review, scope contract, and guardrail rows must
  carry explicit no-dispatch posture. Dispatch-shaped rows are deferred to
  `PB-RETRY-0-B` and require a later lock authority ref.
- Pre-start result:
  pending implementation.

### Edge 2: Many "Single" Retries Could Launder An Unbounded Retry Loop

- Planned containment:
  `programbench_local_retry_lineage_registry@1` must enforce one eligible
  retry request for one `trial_lineage_ref + trial_remand_decision_ref`
  unless a later family grants retry-chain authority.
- Pre-start result:
  pending implementation.

### Edge 3: Accepted Or Blocked Trials Could Become Retry-Ready

- Planned containment:
  eligibility validation must reject locally accepted trials and trials
  blocked by contamination, sandbox violation, hidden/forbidden/source
  evidence, official posture, or missing local remand.
- Pre-start result:
  pending implementation.

### Edge 4: Hidden Or Forbidden Evidence Could Leak Through Remand Source Rows

- Planned containment:
  remand source and retry rationale rows may name local failure/gap categories
  only. They must not include hidden or forbidden paths, names, excerpts,
  semantic summaries, test names, original-source clues, or derived facts.
- Pre-start result:
  pending implementation.

### Edge 5: Retry Rationale Could Be Benchmark Or Model Pressure

- Planned containment:
  allowed retry rationale kinds are local-only. Hidden-test failure, official
  evaluator feedback, source lookup facts, decompilation facts, internet
  lookup facts, external repository facts, benchmark-score pressure, and
  model-ranking pressure are forbidden.
- Pre-start result:
  pending implementation.

### Edge 6: Retry Scope Could Widen The Cleanroom Boundary

- Planned containment:
  scope contracts must separate retry deltas from unchanged context and carry
  unchanged worker-visible source, forbidden source, tool, sandbox, write
  scope, and network hashes. Scope deltas may add only local retry
  instructions or remand-focused obligations.
- Pre-start result:
  pending implementation.

### Edge 7: Slice A Could Prematurely Emit B/C Artifacts

- Planned containment:
  A emits only retry request, lineage registry, remand source index,
  eligibility review, scope contract, and guardrail shapes. Retry dispatch,
  execution capture, candidate delta snapshot, lifecycle projection, outcome
  audit, delta summary, settlement, and family closeout remain absent.
- Pre-start result:
  pending implementation.

### Edge 8: Local Retry Rows Could Become Benchmark Or Ranking Claims

- Planned containment:
  guardrails must reject official ProgramBench participation, hidden-test
  inference, source lookup, official submissions, benchmark truth, benchmark
  score, model ranking, second retry authority, and future-family selection.
- Pre-start result:
  pending implementation.

## Residual Edges

- `PB-RETRY-0-A` is non-executing. `PB-RETRY-0-B` remains the
  execution-adjacent slice and must require its own canonical starter lock,
  dispatch authority ref, sandbox witness contract, and released A refs.
- `PB-RETRY-0-C` remains the settlement slice and must prevent unresolved
  remand pressure from becoming second-retry authority.
- Multi-attempt comparison, model ranking, official ProgramBench participation,
  hidden evaluator integration, benchmark scoring, official submissions,
  broader benchmark result governance, product, graph, release, or
  recursive-policy work remain unselected.

## Current Judgment

- `PB-RETRY-0-A` is ready to be reviewed as the next bounded starter slice.
- The planned slice preserves the intended retry membrane: it can make one
  remand-to-retry candidate reviewable, but it cannot dispatch a retry, run
  commands, materialize retry candidates, widen cleanroom evidence, create
  many single retries, claim benchmark truth, rank models, or select a future
  family.
