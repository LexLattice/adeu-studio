# Assessment vNext+249 Edges

Status: pre-lock edge assessment for `PB-RECON-0-B`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS249_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Rows Could Bypass Released A Workbench Law

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  every B row must bind to released `PB-RECON-0-A` work order, worker context,
  exclusion manifest, sandbox policy, run budget, and guardrail refs.
- Residual:
  local run traces should not validate against ad hoc sandbox or budget rows.

### Edge 2: Candidate Artifact Could Become Official Submission

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  candidate artifact manifests require local workbench artifact posture and no
  official submission authority.
- Residual:
  generated official submissions remain future-family-only.

### Edge 3: Local Run Trace Could Become Open Command Authority

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  local run traces require argv-shaped command rows, command allowlist match,
  released sandbox policy, released run budget, and sandbox attestations.
- Residual:
  implementation must reject raw shell strings, missing allowlist refs, and
  commands outside the released sandbox/write scope.

### Edge 4: Sandbox Or Secret Violation Could Be Treated As Success

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  traces must carry network, secret-absence, write-scope, and sandbox
  attestation refs; sandbox violation refs block successful local evidence.
- Residual:
  later execution harnesses must produce attestations rather than prose-only
  claims.

### Edge 5: Output Capture Could Become Unbounded Evidence Dump

- Pre-lock judgment: `bounded_evidence_only`.
- Planned control:
  stdout/stderr are represented by hashes plus bounded excerpts; filesystem
  side effects require pre/post manifests and diff refs.
- Residual:
  large or binary artifacts need explicit artifact refs and capture policies.

### Edge 6: Probe Result Could Become Benchmark Truth

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  probe result logs require local-probe truth posture and hidden-test
  equivalence non-authority posture.
- Residual:
  `PB-RECON-0-C` may audit local equivalence later, but even local accepted
  status must remain scoped to declared local probes.

### Edge 7: Remand Could Use Hidden Or Forbidden Evidence

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  remand reason sources are closed to local probe failure, local sandbox
  violation, missing required artifact, unsupported behavior gap, or
  inconclusive trace; hidden-test failure, official evaluator feedback,
  original-source observation, and decompilation observation are forbidden.
- Residual:
  postmortem research must not be retroactively admitted as reconstruction
  inference evidence.

### Edge 8: Remand Could Mutate The Released Case Packet

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  remand/correction records require case-packet mutation non-authority and
  semantic route preservation posture.
- Residual:
  case-packet amendment requires a later adapter/reconstruction authority, not
  local worker correction rows.

### Edge 9: Slice B Could Prematurely Emit C Artifacts

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  B emits only candidate artifact manifest, local run trace, probe result log,
  and remand/correction record rows.
- Residual:
  equivalence audit, result summary, handoff, and family closeout alignment
  require `PB-RECON-0-C`.

### Edge 10: B May Be Too Large For One Slice

- Pre-lock judgment: `watch`.
- Planned control:
  if implementation footprint grows too large, split inside the family into
  candidate-artifact/run-trace and probe/remand sub-slices using continuation
  docs, not a new family selector.
- Residual:
  active implementation should stop and remap if validation breadth exceeds
  the starter lock.

## Current Judgment

- `PB-RECON-0-B` is the coherent next slice after the released
  `PB-RECON-0-A` workbench boundary.
- The starter should proceed as a docs/artifacts-only lock bundle before
  implementation.
- Implementation should wait until this `vNext+249` starter bundle is
  accepted.
