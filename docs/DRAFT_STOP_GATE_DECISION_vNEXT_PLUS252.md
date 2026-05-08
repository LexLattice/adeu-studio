# Draft Stop-Gate Decision vNext+252

Status: pre-start decision scaffold for `PB-ATTEMPT-0-B`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+252` / `PB-ATTEMPT-0-B` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS252.md`.
- It does not authorize workbench evidence export, attempt result review,
  remand queue, family closeout alignment, official ProgramBench
  participation, official task execution, official runner integration,
  official evaluator integration, hidden-test handling, hidden-test
  inference, hidden-test equivalence, original source lookup, decompilation,
  internet lookup inside ProgramBench tasks, external repository lookup,
  benchmark submission, benchmark scoring, benchmark truth, model ranking,
  generated official submissions, official submission authority, unbounded
  command execution, target mutation outside the released local sandbox/write
  scope, runtime transition, product authorization, graph-memory authority,
  recursive policy amendment, or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-ATTEMPT-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v79.md` |
| Prior slice closeout present | required | `PB-ATTEMPT-0-A` closed by `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md` |
| Slice-B lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS252.md` drafted |
| Slice scope is bounded | required | invocation record, output capture, candidate materialization, and sandbox application trace only |
| Released A substrate required | required | B rows must consume released attempt request, worker input packet, dispatch preflight, and guardrail refs |
| Invocation cardinality is bounded | required | one invocation per attempt request unless later retry authority is selected |
| Invocation is local-only | required | no official runner/evaluator, hidden-test access, source lookup, internet, decompilation, external repo, Docker socket, or host-secret access |
| Output capture is screened | required | candidate materialization requires forbidden-content screening posture `passed` |
| Materialization stays inside released write scope | required | materialization requires write-scope attestation, generated-file hashes, and `materialized_inside_write_scope = true` |
| Sandbox trace carries absence attestations | required | network, secret, Docker socket, and source lookup absence attestations required |
| Deferred C surfaces stay deferred | required | no workbench evidence export, result review, remand queue, or family closeout alignment |
| Official ProgramBench and benchmark truth stay absent | required | no official submissions, hidden-test equivalence, benchmark score, model ranking, or benchmark truth |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=252` |

## Initial Stop-Gate Posture

- `PB-ATTEMPT-0-B` is the logical second slice after the released
  `PB-ATTEMPT-0-A` attempt-preflight boundary.
- The starter lock is coherent if it remains limited to recording one bounded
  local worker invocation, captured worker output, local candidate
  materialization inside released sandbox write scope, and sandbox application
  trace evidence.
- The implementation must wait until this `vNext+252` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_ATTEMPT_0B_STARTER_LOCK`
- rationale:
  - released `PB-ATTEMPT-0-A` defines the attempt request, exact
    worker-visible input packet, eligibility-only dispatch preflight, and
    non-authority guardrail;
  - `PB-ATTEMPT-0-B` can make the first bounded local invocation and
    materialization evidence reviewable without exporting workbench evidence,
    reviewing results, queuing remands, claiming benchmark truth, creating
    official submissions, ranking models, or selecting a future family;
  - the starter makes input hashes, tool manifests, screening posture,
    write-scope attestation, generated-file hashes, and sandbox absence
    attestations first-class validation edges.
