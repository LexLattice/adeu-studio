# Draft Stop-Gate Decision vNext+251

Status: pre-start decision scaffold for `PB-ATTEMPT-0-A`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+251` / `PB-ATTEMPT-0-A` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS251.md`.
- It does not authorize worker invocation, command execution, candidate
  materialization, local probe execution, workbench evidence export, attempt
  result review, remand queue, official ProgramBench participation, official
  task execution, official runner integration, official evaluator
  integration, hidden-test handling, hidden-test inference, hidden-test
  equivalence, original source lookup, decompilation, internet lookup inside
  ProgramBench tasks, external repository lookup, benchmark submission,
  benchmark scoring, benchmark truth, model ranking, generated official
  submissions, official submission authority, unbounded command execution,
  target mutation outside released local artifacts, runtime transition,
  product authorization, graph-memory authority, recursive policy amendment,
  or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-ATTEMPT-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v79.md` |
| Prior family closeout present | required | `PB-RECON-0` closed by `DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md` |
| Slice-A lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS251.md` drafted |
| Slice scope is bounded | required | attempt request, worker input packet, dispatch preflight, and guardrail only |
| Released `PB-RECON-0` substrate required | required | A rows must consume released work order, worker context, exclusion manifest, sandbox policy, run budget, result summary, and family closeout alignment refs |
| Worker input stays cleanroom-visible only | required | hidden, forbidden, auditor-only, postmortem-only, original-source, decompilation, internet, external-repo, host-secret, and Docker-socket refs stay out of worker-visible material |
| Exclusion summaries are non-content-bearing | required | exclusion summaries may carry category/count/reason/posture/non-exposure only |
| Dispatch preflight is eligibility-only | required | `preflight_scope_posture = eligibility_review_only_no_invocation` |
| Result-summary posture is compatible | required | remand/evidence-gap attempt may consume remand, inconclusive, or missing-evidence posture only |
| Deferred B/C surfaces stay deferred | required | no worker invocation, output capture, candidate materialization, sandbox trace, evidence export, result review, remand queue, or family closeout alignment |
| Official ProgramBench and benchmark truth stay absent | required | no official runner/evaluator, hidden tests, benchmark scores, model rankings, or official submissions |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=251` |

## Initial Stop-Gate Posture

- `PB-ATTEMPT-0-A` is the logical first slice after the released
  `PB-RECON-0` local cleanroom reconstruction workbench boundary.
- The starter lock is coherent if it remains limited to attempt request,
  exact worker-visible input packaging, eligibility-only dispatch preflight,
  and non-authority guardrail.
- The implementation must wait until this `vNext+251` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_ATTEMPT_0A_STARTER_LOCK`
- rationale:
  - released `PB-RECON-0` defines the work order, worker-visible context,
    auditor-only exclusions, sandbox policy, run budget, local result posture,
    and family closeout boundary;
  - `PB-ATTEMPT-0-A` can package a later local attempt request and exact
    worker-visible input without invoking a worker or materializing candidate
    artifacts;
  - the starter keeps exclusion summaries non-content-bearing, preflight
    eligibility-only, and all official ProgramBench, hidden-test, benchmark
    truth, model-ranking, official-submission, and future-family authority
    absent.
