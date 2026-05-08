# Assessment vNext+255 Edges

Status: pre-lock edge assessment for `PB-TRIAL-0-B`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS255_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Rows Could Bypass Released A Trial Law

- Planned containment:
  dispatch, execution capture, candidate snapshot, and lifecycle projection
  rows must bind to released A docket, runbook, sandbox readiness review, and
  non-authority guardrail refs before validation succeeds.
- Required implementation evidence:
  reject missing or mismatched A refs.

### Edge 2: Dispatch Could Proceed Without Ready A Readiness

- Planned containment:
  worker dispatch records require the released A sandbox readiness posture
  `ready_for_later_local_trial_execution_review`.
- Required implementation evidence:
  reject dispatch rows when readiness is blocked, missing, or future-only.

### Edge 3: Dispatch Could Exist Without B-Lock Authority

- Planned containment:
  dispatch records require a `dispatch_authority_ref` tied to the released B
  lock and must not treat A readiness as dispatch authority.
- Required implementation evidence:
  reject missing, stale, or A-sourced dispatch authority refs.

### Edge 4: Multiple Dispatches Could Hide Retries

- Planned containment:
  dispatch cardinality is one specimen per trial docket; retry authority
  remains unselected.
- Required implementation evidence:
  reject second dispatch specimen rows for one docket.

### Edge 5: Dispatch Could Drift From Preflighted Worker Input

- Planned containment:
  dispatch records bind to worker input packet hash, worker-visible context
  hash, tool manifest ref, allowed and forbidden tool manifest hashes, sandbox
  instance ref, sandbox attestation bundle ref, and input packet
  materialization hash.
- Required implementation evidence:
  reject hash drift and missing materialization/sandbox attestation fields.

### Edge 6: Dispatch Could Use Hidden, Source, Internet, Or Secret Channels

- Planned containment:
  dispatch records reject hidden-test access, source lookup, internet lookup,
  decompilation, external repo access, Docker socket access, host-secret
  access, official runner/evaluator contact, benchmark score, model ranking,
  official submission, and retry authority posture.
- Required implementation evidence:
  reject any positive forbidden access posture.

### Edge 7: Execution Capture Could Be Partial Or Prose-Only

- Planned containment:
  execution capture requires transcript/stdout/stderr hashes, bounded
  excerpts, exit code, duration, timeout status, full output capture policy,
  worker tool-call manifest, sandbox witness refs, and explicit capture
  posture.
- Required implementation evidence:
  reject missing hashes, excerpts, or sandbox witness refs.

### Edge 8: Worker Output Could Launder Forbidden Content

- Planned containment:
  forbidden-content screening rows and verdict are required; hidden,
  forbidden-source, postmortem-only, and excluded-derived findings block
  candidate snapshotting.
- Required implementation evidence:
  reject candidate snapshots when screening verdict is not `passed`.

### Edge 9: Candidate Snapshot Could Escape Released Write Scope

- Planned containment:
  snapshots require released write scope, pre/post filesystem manifests,
  fs-diff refs, snapshot manifest hash, generated file hashes, and
  `snapshot_inside_write_scope = true`.
- Required implementation evidence:
  reject outside-scope snapshots and missing generated-file hashes.

### Edge 10: Candidate Snapshot Could Become Official Submission

- Planned containment:
  snapshots are local-only and carry explicit no-official-submission and
  not-benchmark-truth postures.
- Required implementation evidence:
  reject official submission, benchmark truth, or benchmark score posture.

### Edge 11: Lifecycle Projection Could Define New Evidence Law

- Planned containment:
  lifecycle projection maps the trial specimen to released `PB-ATTEMPT-0`
  lifecycle refs and must carry `new_evidence_law_posture` denying new
  evidence-law creation.
- Required implementation evidence:
  reject projection rows that mint new evidence law or bypass attempt
  lifecycle validator bindings.

### Edge 12: B Could Prematurely Emit C Artifacts

- Planned containment:
  B emits only worker dispatch record, execution capture, candidate artifact
  snapshot, and lifecycle projection shapes.
- Required implementation evidence:
  reject outcome audit, observation summary, remand decision, and family
  closeout artifacts in B fixtures.

## Residual Edges

- `PB-TRIAL-0-C` must consume released `PB-TRIAL-0-A/B` refs before outcome
  audit, observation summary, remand decision, or family closeout can occur.
- `PB-TRIAL-0-C` must keep local acceptance scoped to declared local trial
  evidence, not hidden tests or official benchmark results.
- Retry dispatch authority and multi-attempt/model comparison remain
  unselected.
- Official ProgramBench participation, hidden evaluator integration,
  benchmark scoring, model ranking, official submissions, broader benchmark
  result governance, product, graph, release, or recursive-policy work remain
  unselected.

## Current Judgment

- `PB-TRIAL-0-B` is ready as a bounded starter candidate.
- The slice can record one local cleanroom trial specimen, but it cannot audit
  the outcome, grant retry authority, claim benchmark truth, rank models, or
  produce official ProgramBench submissions.
