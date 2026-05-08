# Draft Stop-Gate Decision vNext+250

Status: pre-start decision scaffold for `PB-RECON-0-C`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS250.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+250` / `PB-RECON-0-C` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS250.md`.
- It does not authorize official ProgramBench participation, official task
  execution, official runner integration, official evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, generated official submissions, official
  submission authority, unbounded command execution, target mutation outside
  released local artifacts, runtime transition, product authorization,
  graph-memory authority, recursive policy amendment, or future-family
  selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-RECON-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v78.md` |
| Prior slice closeout present | required | `PB-RECON-0-B` closed by `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS249.md` |
| Slice-C lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS250.md` drafted |
| Slice scope is bounded | required | equivalence audit, result summary, handoff, and family closeout alignment only |
| Released A workbench substrate required | required | C rows must consume released work order, worker context, exclusion manifest, sandbox policy, run budget, and guardrail refs |
| Released B local evidence substrate required | required | C rows must consume candidate artifact manifest, local run trace, probe result log, and remand/correction refs |
| Local equivalence stays local | required | no hidden-test equivalence, official evaluator result, benchmark score, benchmark truth, or model ranking |
| Local accepted gate is strict | required | contamination, sandbox violations, missing evidence, failed required probes, and expectation mismatches block local accepted |
| Handoff remains pressure only | required | no official participation, benchmark-result governance, product, graph, release, recursive-policy, or future-family authority |
| Family closeout closes only `PB-RECON-0` | required | no next-family selection |
| Official ProgramBench and benchmark truth stay absent | required | no official runner/evaluator, hidden tests, benchmark scores, model rankings, or official submissions |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=250` |

## Initial Stop-Gate Posture

- `PB-RECON-0-C` is the logical final slice after the released
  `PB-RECON-0-B` local evidence capture boundary.
- The starter lock is coherent if it remains limited to local audit, local
  result summary, handoff pressure, and family closeout alignment.
- The implementation must wait until this `vNext+250` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_RECON_0C_STARTER_LOCK`
- rationale:
  - released `PB-RECON-0-A` defines the work order, worker-visible context,
    auditor-only exclusions, sandbox policy, run budget, and guardrail;
  - released `PB-RECON-0-B` makes candidate artifacts, local run traces,
    local probe result logs, and remand/correction records reviewable;
  - `PB-RECON-0-C` can now audit local equivalence and close the family
    without claiming hidden-test equivalence, benchmark truth, official
    participation, official submission authority, or model ranking.
