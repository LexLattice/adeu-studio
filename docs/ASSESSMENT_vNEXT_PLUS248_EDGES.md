# Assessment vNext+248 Edges

Status: pre-lock edge assessment for `PB-RECON-0-A`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS248_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Work Order Could Become Worker Dispatch Authority

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  work orders require `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_recon_0a` and execution
  non-authority posture.
- Residual:
  worker dispatch and reconstruction execution require a later slice or
  family lock.

### Edge 2: Blocked Or Contaminated Case Packet Could Become Work Order

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  work orders require released case packet, readiness, and handoff refs, plus
  ready posture, clean contamination, and empty carried blockers.
- Residual:
  warning-ready cases may be represented only if warnings are non-exposure and
  non-authority issues.

### Edge 3: Worker Context Could Leak Hidden Or Forbidden Refs

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  worker context packets are worker-facing and may contain only
  cleanroom-visible, worker-authorized refs. Hidden, forbidden,
  postmortem-only, original-source, decompilation, external-repo,
  Docker-socket, host-secret, and excluded derived-summary refs fail closed.
- Residual:
  future implementation must keep worker context physically separate from
  auditor-only ledgers.

### Edge 4: Exclusion Manifest Could Become Worker Evidence

- Pre-lock judgment: `auditor_only`.
- Planned control:
  exclusion manifests carry hidden, forbidden, postmortem-only, and excluded
  derived-summary refs for audit only and must not be served into worker
  context.
- Residual:
  UI or worker-harness surfaces must not render exclusion manifest contents as
  worker-visible context without a later authority review.

### Edge 5: Derived Summary Could Launder Forbidden Evidence

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  derived summaries from forbidden or hidden evidence are excluded from worker
  context and represented only as auditor-only exclusion rows when needed.
- Residual:
  postmortem research remains possible only outside inference context.

### Edge 6: Sandbox Policy Could Become Open Command Authority

- Pre-lock judgment: `non_execution_boundary_only`.
- Planned control:
  sandbox policies define network, filesystem, dependency, environment,
  command-shape, write-scope, timeout, resource, secret, Docker socket,
  source-lookup, decompilation, and external-repo policy but grant no command
  execution authority in A.
- Residual:
  later local run traces must bind to released sandbox policy, command
  allowlist, sandbox attestation, and budget rows.

### Edge 7: Run Budget Could Grant Execution Authority

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  run budgets constrain future candidate, run, probe, remand, timeout, token,
  and filesystem limits but require non-execution budget authority posture.
- Residual:
  execution requires a later selected local reconstruction slice.

### Edge 8: Slice A Could Include B/C Execution-Adjacent Artifacts

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  A emits only work order, worker context, exclusion manifest, sandbox policy,
  run budget, and guardrail rows. Candidate artifacts, run traces, probe logs,
  remand records, equivalence audits, summaries, handoffs, and family
  closeout rows are deferred.
- Residual:
  B may need to split into B1/B2 if execution-adjacent validation grows.

### Edge 9: Official ProgramBench Scope Could Leak In

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  guardrails reject official ProgramBench participation, runner/evaluator
  integration, hidden-test inference, hidden-test equivalence, official
  submissions, benchmark scoring, benchmark truth, and model ranking.
- Residual:
  official participation and benchmark-result governance remain possible
  later families only.

### Edge 10: Bundle Forward Refs Could Mask Mismatched Rows

- Pre-lock judgment: `requires_bundle_resolution`.
- Planned control:
  validation should resolve work order, worker context, exclusion manifest,
  sandbox policy, run budget, and guardrail refs as one bundle and reject
  dangling, mismatched, or cross-task refs.
- Residual:
  implementation should avoid validating each row in isolation when row
  linkage is the safety property.

## Current Judgment

- `PB-RECON-0-A` is the coherent first slice after the released
  `PB-ADAPTER-0` cleanroom adapter substrate.
- The starter should proceed as a docs/artifacts-only lock bundle before
  implementation.
- Implementation should wait until this `vNext+248` starter bundle is
  accepted.
