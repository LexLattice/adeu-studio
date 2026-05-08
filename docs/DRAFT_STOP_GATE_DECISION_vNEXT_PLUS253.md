# Draft Stop-Gate Decision vNext+253

Status: pre-start decision scaffold for `PB-ATTEMPT-0-C`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS253.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+253` / `PB-ATTEMPT-0-C` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS253.md`.
- It does not authorize official ProgramBench participation, official task
  execution, official runner integration, official evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, generated official submissions, official
  submission authority, worker invocation, command execution, new candidate
  materialization outside released B rows, retry dispatch authority, runtime
  transition, product authorization, graph-memory authority, recursive policy
  amendment, or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-ATTEMPT-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v79.md` |
| Prior slice closeout present | required | `PB-ATTEMPT-0-B` closed by `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md` |
| Slice-C lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS253.md` drafted |
| Slice scope is bounded | required | workbench evidence export, attempt result review, remand queue, and attempt family closeout alignment only |
| Released A substrate required | required | C rows must consume released attempt request, worker input packet, dispatch preflight, and guardrail refs |
| Released B substrate required | required | C rows must consume released invocation, output capture, candidate materialization, and sandbox trace refs |
| Released PB-RECON validation required | required | evidence export must bind to `PB-RECON-0` validator binding refs and validation result refs |
| Export laundering is blocked | required | valid export cannot treat attempt output as accepted workbench evidence without released workbench validation |
| Local acceptance is scoped | required | accepted attempt posture requires exported workbench local-accepted summaries and remains local-only |
| Remand queue is pressure-only | required | remand rows carry local retry pressure but no retry dispatch authority |
| Family closeout is bounded | required | closeout alignment closes only `PB-ATTEMPT-0-A/B/C` |
| Official ProgramBench and benchmark truth stay absent | required | no official submissions, hidden-test equivalence, benchmark score, model ranking, or benchmark truth |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=253` |

## Initial Stop-Gate Posture

- `PB-ATTEMPT-0-C` is the logical final slice after the released
  `PB-ATTEMPT-0-B` invocation-capture boundary.
- The starter lock is coherent if it remains limited to exporting local
  attempt evidence into released `PB-RECON-0` workbench vocabulary, reviewing
  local attempt posture, recording pressure-only remand queues, and closing
  only `PB-ATTEMPT-0`.
- The implementation must wait until this `vNext+253` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_ATTEMPT_0C_STARTER_LOCK`
- rationale:
  - released `PB-ATTEMPT-0-A` defines the attempt request, exact
    worker-visible input packet, eligibility-only dispatch preflight, and
    non-authority guardrail;
  - released `PB-ATTEMPT-0-B` records the bounded local invocation, screened
    output capture, candidate materialization, and sandbox application trace;
  - `PB-ATTEMPT-0-C` can now make export, local result review, remand queue,
    and family closeout rows reviewable without granting retry authority,
    official ProgramBench authority, hidden-test equivalence, benchmark
    truth, model ranking, official submission, or future-family selection;
  - the starter makes `PB-RECON-0` validator bindings and validation result
    refs first-class so attempt evidence cannot launder itself into accepted
    workbench evidence.
