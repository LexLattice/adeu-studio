# Draft Stop-Gate Decision vNext+246

Status: pre-start decision scaffold for `PB-ADAPTER-0-B`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS246.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+246` / `PB-ADAPTER-0-B` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS246.md`.
- It does not authorize `PB-ADAPTER-0-C`, reconstruction case packets,
  readiness summaries, handoffs, family closeout alignment, official
  ProgramBench participation, official task execution, official runner
  integration, hidden-test handling, hidden-test inference, original source
  lookup, decompilation, internet lookup inside ProgramBench tasks, external
  repository lookup, benchmark submission, benchmark scoring, benchmark truth,
  model ranking, generated official submissions, arbitrary command execution,
  target mutation, runtime transition, product authorization, graph-memory
  authority, recursive policy amendment, or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-ADAPTER-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v77.md` |
| Slice-A closeout present | required | `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS245.md` and `ASSESSMENT_vNEXT_PLUS245_EDGES.md` close A |
| Slice-B lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS246.md` drafted |
| Slice scope is bounded | required | probe plan, observation log, I/O artifact index, and filesystem side-effect observation only |
| Released A substrate required | required | B rows must consume released task intake, artifact manifest, visibility manifest, access contract, and guardrail refs |
| Probe command shape is constrained | required | argv-shaped commands required unless shell wrapping is explicitly declared with reason |
| Local probe evidence stays non-authoritative | required | no hidden-test equivalence, benchmark truth, model ranking, official runner, or generated submission authority |
| Later surfaces deferred | required | case packets, readiness summaries, handoffs, family closeout alignment, official participation, and benchmark results deferred |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=246` |

## Recommendation

- gate decision:
  - `READY_TO_REVIEW_PB_ADAPTER_0B_STARTER_LOCK`
- rationale:
  - `PB-ADAPTER-0-B` is the next narrow slice after `PB-ADAPTER-0-A`;
  - it makes active local/reference probe evidence reviewable under the
    released cleanroom access contract without granting official benchmark or
    open command authority;
  - it keeps reconstruction case packets, readiness summaries, official
    evaluator integration, generated submissions, benchmark scores, and model
    ranking out of scope.

## Open Pre-Implementation Notes

- External review should check whether the command-shape contract is strict
  enough to block raw shell authority while still representing intended local
  probes.
- External review should check whether stdout/stderr/exit/filesystem
  observation rows are normalized enough for later case packet assembly.
- External review should check whether B consumes released A refs without
  reclassifying hidden or forbidden evidence as probe evidence.
