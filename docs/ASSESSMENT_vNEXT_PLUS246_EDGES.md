# Assessment vNext+246 Edges

Status: pre-lock edge assessment for `PB-ADAPTER-0-B`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS246_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Probe Plan Could Become Open Command Authority

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  probe command rows must be argv-shaped by default and must not be raw shell
  strings unless explicitly marked `shell_wrapped_with_reason`.
- Residual:
  implementation should reject shell-shaped command payloads that lack a
  declared wrapper reason and bounded command scope.

### Edge 2: Observation Rows Could Bypass Released A Access Contract

- Pre-lock judgment: `requires_released_a_refs`.
- Planned control:
  every probe plan and observation row must resolve to released
  `PB-ADAPTER-0-A` task intake, visibility manifest, worker access contract,
  and guardrail refs.
- Residual:
  B must not reassemble a different task surface from loose source refs.

### Edge 3: Probe Observation Could Become Hidden-Test Equivalence

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  local/reference probe rows require hidden-test-equivalence posture that keeps
  observations as reconstruction evidence only.
- Residual:
  later readiness summaries must still decide whether observation coverage is
  sufficient; B itself cannot make that readiness claim.

### Edge 4: Hidden Or Forbidden Evidence Could Become Probe Evidence

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  hidden evaluator, original source, decompilation, internet, external repo,
  host-secret, and Docker-socket sources remain forbidden or hidden for
  inference and cannot be cited as observation evidence.
- Residual:
  postmortem-only material remains outside reconstruction inference unless a
  later family selects hidden-result governance.

### Edge 5: Local Probe Pass Could Become Benchmark Truth

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  observation rows must preserve local probe not truth / not benchmark score /
  not model ranking posture.
- Residual:
  official ProgramBench participation and benchmark result governance remain
  unselected.

### Edge 6: Filesystem Side Effects Could Widen Target Scope

- Pre-lock judgment: `requires_path_scope_contract`.
- Planned control:
  side-effect observation rows must record created, modified, deleted, and
  untouched path refs under bounded path-scope posture.
- Residual:
  B should reject side-effect rows outside the released access contract and
  allowed write scope.

### Edge 7: Observation Logs Could Store Unbounded Output

- Pre-lock judgment: `requires_bounded_excerpt_hash`.
- Planned control:
  stdout and stderr observations should record hashes plus bounded excerpts,
  not unbounded captured streams.
- Residual:
  large binary or directory artifacts should be represented by artifact refs
  and hashes rather than embedded payloads.

### Edge 8: B Could Prematurely Create Case Packets Or Readiness

- Pre-lock judgment: `must_defer_c_surface`.
- Planned control:
  `PB-ADAPTER-0-B` emits only probe plan, observation log, I/O artifact index,
  and filesystem side-effect observation shapes.
- Residual:
  reconstruction case packets, readiness summaries, handoffs, and family
  closeout alignment remain `PB-ADAPTER-0-C`.

## Current Judgment

- `PB-ADAPTER-0-B` is a coherent second slice after `PB-ADAPTER-0-A`.
- The starter should proceed as a docs/artifacts-only lock bundle before
  implementation.
- Implementation should wait until this `vNext+246` starter bundle is accepted.
