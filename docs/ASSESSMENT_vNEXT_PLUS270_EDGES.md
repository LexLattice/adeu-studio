# Assessment vNext+270 Edges

Status: post-closeout edge assessment for `PB-SINGLE-CASE-RUN-0-B`.

Authority layer: closeout / implementation evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS270_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Closed Edge Review

### Edge 1: A Preflight Could Be Treated As Dispatch Authority

- Closeout result:
  contained.
- Evidence:
  B requires released A rows plus a B-slice dispatch authority ref and
  dispatch authority kind. A-only preflight evidence does not validate as a
  dispatch specimen.

### Edge 2: Multiple Dispatches Could Hide Behind One Case

- Closeout result:
  contained.
- Evidence:
  B requires `dispatch_specimen_index = 1` and
  `single_case_dispatch_cardinality_posture =
  exactly_one_dispatch_specimen`; duplicate dispatch rows for one A request are
  rejected.

### Edge 3: Command Capture Could Become Open Shell Authority

- Closeout result:
  contained, including review hardening.
- Evidence:
  execution traces require argv-shaped command rows and reject raw shell
  strings. Review feedback expanded the rejection surface to shell executable
  path basenames and shell control/redirection markers, so `/bin/sh`, `bash`,
  `cmd.exe`, `&&`, `|`, and redirect-shaped command rows fail closed.

### Edge 4: Sandbox Witnesses Could Be Narrative Only

- Closeout result:
  contained.
- Evidence:
  B requires concrete sandbox instance, attestation bundle, network mode,
  Docker socket absence, secret absence, source lookup absence, decompilation
  absence, and write-scope attestation refs.

### Edge 5: Worker Output Could Launder Forbidden Content Into Artifacts

- Closeout result:
  contained, including review hardening.
- Evidence:
  candidate artifact capture requires
  `forbidden_content_screen_verdict = passed`, generated artifacts inside the
  released write scope, materialization input/output hashes, and generated
  artifact rows that match declared artifact hash rows.

### Edge 6: Lifecycle Projection Could Become New Outcome Truth

- Closeout result:
  contained.
- Evidence:
  lifecycle projection binds released lifecycle refs and validator refs while
  retaining non-new-truth and non-hidden-test-equivalence posture. It does not
  mint benchmark truth.

### Edge 7: B Could Collapse Into C Outcome Audit

- Closeout result:
  contained.
- Evidence:
  B emits specimen capture/projection surfaces only. Local outcome audit,
  observation summary, remand/acceptance decision, pressure-only handoff, and
  family closeout remain deferred to `PB-SINGLE-CASE-RUN-0-C`.

## Review Feedback Integrated

- Codex review:
  candidate artifact rows must match their declared generated artifact hashes;
  stale or mismatched hash rows now fail validation.
- Gemini review:
  argv-shaped command validation now rejects shell executable path basenames
  and broader shell marker strings, not only exact `sh` / `bash` tokens.

## Residual Edges

- Local outcome audit remains deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Observation summary remains deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Remand or acceptance decision remains deferred to `PB-SINGLE-CASE-RUN-0-C`.
- Pressure-only handoff and full family closeout remain deferred to
  `PB-SINGLE-CASE-RUN-0-C`.
- Official ProgramBench runner/evaluator integration remains unselected.
- Hidden-test handling and hidden-test equivalence remain unselected.
- Benchmark scoring, baseline comparison, and model ranking remain unselected.
- Batch execution over a matrix remains unselected.
- Retry authority remains unselected.
- Future-family selection remains unselected by this closeout.

## Current Judgment

`PB-SINGLE-CASE-RUN-0-B` is closed on `main`. The implementation is
action-adjacent but bounded: it captures one local specimen and lifecycle
projection without audit, acceptance, retry, scoring, model ranking, official
participation, or future-family authority.
