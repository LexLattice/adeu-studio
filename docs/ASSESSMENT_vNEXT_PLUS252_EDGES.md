# Assessment vNext+252 Edges

Status: pre-lock edge assessment for `PB-ATTEMPT-0-B`.

Authority layer: planning / pre-lock assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS252_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Rows Could Bypass Released A Attempt Law

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  invocation, output capture, materialization, and sandbox trace rows must bind
  to released attempt request, worker input packet, dispatch preflight, and
  non-authority guardrail refs.
- Residual:
  implementation must reject orphaned or mismatched A refs.

### Edge 2: Blocked Preflight Could Still Produce Invocation Rows

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  worker invocation records cannot validate unless the released A dispatch
  preflight is passed for later local attempt review.
- Residual:
  preflight repair remains A/remand territory, not B invocation territory.

### Edge 3: Multiple Invocations Could Hide Retries

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  one worker invocation per attempt request unless a later lock introduces
  retry parent and retry authority rows.
- Residual:
  retry orchestration is unselected.

### Edge 4: Invocation Could Drift From The Preflighted Input Packet

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  invocation records require input packet hash, worker-visible context hash,
  tool manifest ref, allowed tool manifest hash, and forbidden tool manifest
  hash.
- Residual:
  C must continue to treat these as evidence boundaries, not benchmark truth.

### Edge 5: Invocation Could Use Hidden, Source, Internet, Or Secret Channels

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  invocation and sandbox trace rows reject hidden-test access, source lookup,
  internet lookup, decompilation, external repo access, Docker socket access,
  host-secret access, and official runner/evaluator contact.
- Residual:
  mechanical sandbox implementation details remain local harness work, not
  official ProgramBench integration.

### Edge 6: Worker Output Could Launder Forbidden Content

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  output capture requires forbidden-content screening posture, and
  materialization is blocked unless the posture is `passed`.
- Residual:
  inconclusive screening must route to review, not materialization.

### Edge 7: Bounded Excerpts Could Replace Output Hashes

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  output capture rows require output hashes and bounded excerpts; excerpts are
  advisory/debug evidence, not complete output identity.
- Residual:
  C export must preserve hash identity.

### Edge 8: Candidate Materialization Could Escape Released Write Scope

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  materialization rows require write-scope ref, write-scope attestation,
  materialization input hash, materialization output manifest hash, generated
  file hashes, and `materialized_inside_write_scope = true`.
- Residual:
  target mutation outside released local sandbox remains forbidden.

### Edge 9: Sandbox Trace Could Become Official Execution Or Evaluation

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  sandbox application traces describe local sandbox application only and
  cannot claim official ProgramBench execution, official evaluator contact,
  hidden-test equivalence, benchmark score, model ranking, or official
  submission.
- Residual:
  official participation remains unselected.

### Edge 10: Candidate Materialization Could Become Official Submission

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  candidate materialization requires local-only posture, no official
  submission posture, and no benchmark truth posture.
- Residual:
  generated official submission review remains unselected.

### Edge 11: B Could Prematurely Emit C Artifacts

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  B emits only invocation record, output capture, candidate materialization,
  and sandbox application trace shapes.
- Residual:
  evidence export, result review, remand queue, and family closeout alignment
  remain `PB-ATTEMPT-0-C` territory.

### Edge 12: B Rows Could Select Future Family Or Rank Models

- Pre-lock judgment: `must_fail_closed`.
- Planned control:
  invocation and materialization rows carry no future-family selection,
  benchmark score, leaderboard, or model-ranking authority.
- Residual:
  future arc selection remains operator/selector work after family closeout.

## Current Judgment

- `PB-ATTEMPT-0-B` is the coherent next slice after the released
  `PB-ATTEMPT-0-A` attempt-preflight boundary.
- The starter should proceed as a docs-only lock bundle before implementation.
- Implementation should wait until this `vNext+252` starter bundle is
  accepted.
