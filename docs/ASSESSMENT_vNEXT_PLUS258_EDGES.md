# Assessment vNext+258 Edges

Status: post-closeout edge assessment for `PB-RETRY-0-B`.

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS258_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Dispatch Could Bypass Released A Retry Law

- Closeout state:
  contained.
- Evidence:
  `validate_pb_retry_0b_dispatch_bundle` consumes released A retry request,
  lineage registry, remand source index, eligibility review, scope contract,
  and guardrail rows before B dispatch can validate.

### Edge 2: A Eligibility Could Be Treated As Dispatch Authority

- Closeout state:
  contained.
- Evidence:
  retry dispatch rows require `retry_dispatch_authority_ref =
  docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md`; A eligibility remains a
  prerequisite only.

### Edge 3: A Eligibility Could Come From Another Retry Request

- Closeout state:
  contained after review fix.
- Evidence:
  review hardening requires the eligibility row to reference the same retry
  request, lineage registry, scope contract, and guardrail passed to bundle
  validation.

### Edge 4: Multiple Retry Dispatches Could Hide A Retry Loop

- Closeout state:
  contained.
- Evidence:
  dispatch rows require `retry_depth = 1` and
  `one_retry_dispatch_specimen_per_retry_request`; existing retry request refs
  remain blocking for this slice.

### Edge 5: Dispatch Could Drift From Source Trial Inputs Or Tools

- Closeout state:
  contained after review fix.
- Evidence:
  validation rejects worker input packet hash, worker-visible context hash,
  tool manifest ref, allowed tool hash, forbidden tool hash, or input
  materialization hash drift from the source trial dispatch.

### Edge 6: Dispatch Could Drift From Released A Cleanroom Scope

- Closeout state:
  contained.
- Evidence:
  validation binds retry scope delta hash and unchanged sandbox policy hash to
  released A scope contract values.

### Edge 7: Execution Capture Could Launder Hidden Or Forbidden Evidence

- Closeout state:
  contained.
- Evidence:
  execution capture rows require forbidden-content screening basis refs,
  screened output hashes, bounded excerpts, and no sandbox violations before
  downstream materialization can validate.

### Edge 8: Candidate Delta Snapshot Could Materialize Before Screening

- Closeout state:
  contained.
- Evidence:
  candidate delta snapshots require `forbidden_content_screen_verdict =
  passed`; bundle validation also requires the materialization input hash to
  appear in screened output hashes.

### Edge 9: Candidate Delta Snapshot Could Escape Released Write Scope

- Closeout state:
  contained.
- Evidence:
  bundle validation requires retry candidate delta write scope to match the
  source trial candidate snapshot write scope and `inside_released_write_scope
  = true`.

### Edge 10: Lifecycle Projection Could Define New Evidence Law

- Closeout state:
  contained.
- Evidence:
  retry lifecycle projection requires released trial/attempt lifecycle
  posture and rejects `new_evidence_law_posture` drift.

### Edge 11: Sandbox Trace Could Become Narrative Rather Than Witnessed

- Closeout state:
  contained.
- Evidence:
  sandbox trace rows require explicit witness refs for network, Docker socket,
  host secret, source lookup, decompilation, write scope, resource limits, and
  tool-manifest matching, and bundle validation rejects violation refs.

### Edge 12: B Could Prematurely Emit C Artifacts

- Closeout state:
  contained.
- Evidence:
  B emits only dispatch record, execution capture, candidate delta snapshot,
  lifecycle projection, and sandbox application trace shapes. Outcome audit,
  delta summary, remand settlement, and family closeout remain deferred to
  `PB-RETRY-0-C`.

## Residual Edges

- `PB-RETRY-0-C` must consume released `PB-RETRY-0-A/B` refs before outcome
  audit, same-lineage delta summary, remand settlement, or closeout can occur.
- `PB-RETRY-0-C` must prevent local remand settlement from becoming
  second-retry authority.
- `PB-RETRY-0-C` must keep same-lineage delta observations local-only and not
  model-ranking, benchmark-ranking, hidden-test, or leaderboard claims.

## Current Judgment

`PB-RETRY-0-B` is closed. The next bounded slice is `PB-RETRY-0-C`.
