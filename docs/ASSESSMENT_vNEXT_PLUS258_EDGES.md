# Assessment vNext+258 Edges

Status: pre-lock edge assessment for `PB-RETRY-0-B`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS258_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Dispatch Could Bypass Released A Retry Law

- Planned containment:
  B bundle validation must consume released A retry request, lineage registry,
  remand source index, eligibility review, scope contract, and guardrail rows.
- Pre-start result:
  pending implementation.

### Edge 2: A Eligibility Could Be Treated As Dispatch Authority

- Planned containment:
  dispatch records must require `retry_dispatch_authority_ref` tied to the
  released B lock. A eligibility remains a prerequisite only.
- Pre-start result:
  pending implementation.

### Edge 3: Multiple Retry Dispatches Could Hide A Retry Loop

- Planned containment:
  dispatch rows must enforce one dispatch specimen per retry request and keep
  retry depth within released A `retry_depth_limit`.
- Pre-start result:
  pending implementation.

### Edge 4: Dispatch Could Drift From Released A Cleanroom Boundary

- Planned containment:
  dispatch rows must bind retry input packet, worker-visible context, scope
  contract, tool manifests, sandbox policy, run budget, sandbox instance,
  sandbox attestation bundle, and input materialization hashes to released A
  scope.
- Pre-start result:
  pending implementation.

### Edge 5: Execution Capture Could Launder Hidden Or Forbidden Evidence

- Planned containment:
  execution capture must reject hidden-test, official-evaluator,
  original-source, source-lookup, decompilation, internet, external-repo,
  host-secret, Docker-socket, postmortem-only, and excluded-derived evidence.
- Pre-start result:
  pending implementation.

### Edge 6: Candidate Delta Snapshot Could Materialize Before Screening

- Planned containment:
  candidate delta snapshot validation must require
  `forbidden_content_screen_verdict = passed` and screened output hashes that
  match materialization input hashes.
- Pre-start result:
  pending implementation.

### Edge 7: Candidate Delta Snapshot Could Escape Released Write Scope

- Planned containment:
  snapshot rows must require released write scope refs and
  `inside_released_write_scope = true`.
- Pre-start result:
  pending implementation.

### Edge 8: Lifecycle Projection Could Define New Evidence Law

- Planned containment:
  lifecycle projection rows may map retry evidence to released trial/attempt
  validator bindings only and must carry no-new-evidence-law posture.
- Pre-start result:
  pending implementation.

### Edge 9: Sandbox Trace Could Become Narrative Rather Than Witnessed

- Planned containment:
  sandbox application traces must carry concrete witness refs for network,
  Docker socket, host secret, source lookup, decompilation, write scope,
  resource limit, and tool-manifest posture.
- Pre-start result:
  pending implementation.

### Edge 10: B Could Prematurely Emit C Artifacts

- Planned containment:
  B emits only dispatch record, execution capture, candidate delta snapshot,
  lifecycle projection, and sandbox application trace. Outcome audit, retry
  delta summary, remand settlement, and family closeout remain deferred to
  `PB-RETRY-0-C`.
- Pre-start result:
  pending implementation.

## Residual Edges

- `PB-RETRY-0-B` is execution-adjacent and must be reviewed carefully before
  implementation.
- `PB-RETRY-0-C` must consume released A/B refs before outcome audit, retry
  delta summary, remand settlement, or family closeout can occur.
- `PB-RETRY-0-C` must keep remand settlement local-only and prevent unresolved
  pressure from becoming second-retry authority.
- Official ProgramBench participation, hidden evaluator integration,
  benchmark scoring, model ranking, official submissions, broader benchmark
  result governance, product, graph, release, or recursive-policy work remain
  unselected.

## Current Judgment

- `PB-RETRY-0-B` is ready to be reviewed as the next bounded starter slice.
- The planned slice may record one local retry dispatch specimen and local
  evidence under released A retry-intake law, but it cannot claim benchmark
  truth, rank models, authorize official submission, settle remand, grant a
  second retry, or select a future family.
