# Assessment vNext+270 Edges

Status: pre-lock edge assessment for `PB-SINGLE-CASE-RUN-0-B`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS270_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: A Preflight Could Be Treated As Dispatch Authority

- Risk:
  a ready A preflight packet could be treated as permission to run a worker.
- Required containment:
  B must require a `b_slice_dispatch_authority_ref` and
  `dispatch_authority_kind = b_slice_lock_local_single_specimen_only`.

### Edge 2: Multiple Dispatches Could Hide Behind One Case

- Risk:
  one selected case could be run repeatedly while still being described as a
  single-case specimen.
- Required containment:
  B must require `dispatch_specimen_index = 1`,
  `single_case_dispatch_cardinality_posture =
  exactly_one_dispatch_specimen`, and reject duplicate dispatch rows for one A
  request.

### Edge 3: Command Capture Could Become Open Shell Authority

- Risk:
  execution trace rows could carry raw shell strings or unbounded command
  authority.
- Required containment:
  B must require argv-shaped command rows and reject raw shell strings unless a
  later explicit authority grants and justifies shell wrapping.

### Edge 4: Sandbox Witnesses Could Be Narrative Only

- Risk:
  execution could claim sandbox safety without binding concrete witness refs.
- Required containment:
  B must require sandbox instance, sandbox attestation, network mode, Docker
  socket absence, secret absence, source lookup absence, decompilation absence,
  and write-scope attestation refs.

### Edge 5: Worker Output Could Launder Forbidden Content Into Artifacts

- Risk:
  captured worker output could contain hidden, forbidden, postmortem-only, or
  excluded-derived material and still be materialized as a candidate artifact.
- Required containment:
  candidate artifact capture must require
  `forbidden_content_screen_verdict = passed`, generated artifacts inside
  released write scope, and materialization hashes that bind captured output.

### Edge 6: Lifecycle Projection Could Become New Outcome Truth

- Risk:
  lifecycle projection could be read as benchmark truth or hidden-test
  equivalence.
- Required containment:
  projection rows must state that they are not new truth, bind released
  validator refs, and keep benchmark truth posture negative.

### Edge 7: B Could Collapse Into C Outcome Audit

- Risk:
  B could record acceptance/remand or local outcome posture instead of only
  execution/capture/projection evidence.
- Required containment:
  local outcome audit, observation summary, remand/acceptance decision, and
  handoff rows remain deferred to `PB-SINGLE-CASE-RUN-0-C`.

## Residual Edges

- Local outcome audit remains deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Remand or acceptance decision remains deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Official ProgramBench runner/evaluator integration remains unselected.
- Hidden-test handling and hidden-test equivalence remain unselected.
- Benchmark scoring, baseline comparison, and model ranking remain unselected.
- Batch execution over a matrix remains unselected.
- Retry authority remains unselected.
- Future-family selection remains unselected by this starter.

## Current Judgment

The `PB-SINGLE-CASE-RUN-0-B` starter is action-adjacent but bounded enough to
proceed to implementation after `make arc-start-check ARC=270` passes.
