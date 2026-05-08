# Assessment vNext+251 Edges

Status: pre-lock edge assessment for `PB-ATTEMPT-0-A`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS251_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: A Rows Could Bypass Released `PB-RECON-0` Workbench Law

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  attempt request, worker input packet, preflight, and guardrail rows must
  bind to released `PB-RECON-0` work order, worker context, exclusion
  manifest, sandbox policy, run budget, result summary, and family closeout
  refs.
- Residual:
  implementation must reject orphaned or mismatched workbench refs.

### Edge 2: Incompatible Workbench Result Summary Could Become Attempt Substrate

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  remand/evidence-gap attempts may consume only `local_remand_required`,
  `inconclusive_local_audit`, or `blocked_by_missing_evidence` with explicit
  purpose; local accepted, contamination-blocked, sandbox-violation-blocked,
  and future-family-only summaries are blocked.
- Residual:
  future accepted-result replay or benchmark participation needs a separate
  lock.

### Edge 3: Worker Input Packet Could Leak Auditor-Only Or Forbidden Refs

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  worker-visible refs must be subsets of released worker-visible context and
  allowed advisory refs; auditor-only, hidden, forbidden, postmortem-only,
  original-source, decompilation, internet, external-repo, host-secret, and
  Docker-socket refs are rejected.
- Residual:
  B/C must preserve this boundary during output capture and evidence export.

### Edge 4: Exclusion Summary Could Launder Forbidden Evidence

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  exclusion summary rows may carry only category, count, reason code,
  authority posture, and non-exposure statement; source paths, source names,
  content excerpts, semantic summaries, derived facts, test names, hidden
  artifact ids, and original-source clues are rejected.
- Residual:
  summaries must stay non-content-bearing even when useful for audit.

### Edge 5: Worker Input Manifest Could Be Non-Replayable

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  worker input packets require worker input manifest hash, worker-visible ref
  count, and forbidden-ref exposure check hash.
- Residual:
  B must bind invocation records to the input packet hash.

### Edge 6: Dispatch Preflight Could Become Worker Invocation Authority

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  preflight requires
  `preflight_scope_posture = eligibility_review_only_no_invocation` and no
  worker dispatch or command execution authority.
- Residual:
  worker invocation remains `PB-ATTEMPT-0-B` territory.

### Edge 7: Guardrail Could Miss Official Or Benchmark Authority

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  non-authority guardrail rows reject official ProgramBench participation,
  hidden-test inference, source lookup, official submission, benchmark truth,
  model ranking, and future-family selection authority.
- Residual:
  official participation governance remains unselected.

### Edge 8: Slice A Could Prematurely Emit B/C Artifacts

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  A emits only attempt request, worker input packet, dispatch preflight, and
  non-authority guardrail shapes.
- Residual:
  worker invocation, output capture, candidate materialization, sandbox
  application trace, evidence export, result review, remand queue, and family
  closeout alignment remain deferred.

### Edge 9: Attempt Request Could Become Model Ranking

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  worker profile refs are context only; model-ranking posture is
  non-authoritative.
- Residual:
  model comparison experiments remain unselected.

### Edge 10: Attempt Request Could Select Future Family

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  attempt guardrail and preflight carry no future-family selection posture.
- Residual:
  future arc selection remains operator/selector work after family closeout.

## Current Judgment

- `PB-ATTEMPT-0-A` is the coherent next slice after the released
  `PB-RECON-0` local cleanroom reconstruction workbench boundary.
- The starter should proceed as a docs-only lock bundle before implementation.
- Implementation should wait until this `vNext+251` starter bundle is
  accepted.
