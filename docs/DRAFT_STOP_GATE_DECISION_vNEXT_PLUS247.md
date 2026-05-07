# Draft Stop-Gate Decision vNext+247

Status: pre-start decision scaffold for `PB-ADAPTER-0-C`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS247.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+247` / `PB-ADAPTER-0-C` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS247.md`.
- It does not authorize reconstruction execution, generated Python
  implementation, generated official submissions, official ProgramBench
  participation, official task execution, official runner integration,
  official evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, original source lookup, decompilation, internet
  lookup inside ProgramBench tasks, external repository lookup, benchmark
  submission, benchmark scoring, benchmark truth, model ranking, arbitrary
  command execution, target mutation, runtime transition, product
  authorization, graph-memory authority, recursive policy amendment, or
  future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-ADAPTER-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v77.md` |
| Slice-A closeout present | required | `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS245.md` and `ASSESSMENT_vNEXT_PLUS245_EDGES.md` close A |
| Slice-B closeout present | required | `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS246.md` and `ASSESSMENT_vNEXT_PLUS246_EDGES.md` close B |
| Slice-C lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS247.md` drafted |
| Slice scope is bounded | required | case packet, readiness summary, handoff, and family closeout alignment only |
| Released A/B substrate required | required | C rows must consume released intake, visibility, access, guardrail, probe, observation, I/O artifact, and side-effect refs |
| Case packet lineage is bounded | required | task intake, artifact manifest, visibility manifest, access contract, guardrails, probes, observations, I/O artifacts, and side-effect rows must align |
| Contamination blocks readiness | required | non-clean contamination, hidden/forbidden exposure, derived-summary exposure, access violation, or probe-scope violation cannot be ready |
| Local probe evidence stays non-authoritative | required | local probes remain reconstruction evidence only, not benchmark truth, hidden-test equivalence, score, or model ranking |
| Handoff stays non-authoritative | required | no implementation, execution, official ProgramBench, benchmark-result, or future-family authority |
| Family closeout closes only selected family | required | closeout alignment may close `PB-ADAPTER-0` only |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=247` |

## Initial Stop-Gate Posture

- `PB-ADAPTER-0-C` is the logical final slice after the released A and B
  substrate.
- The starter lock is coherent if it remains limited to packet assembly,
  readiness review, handoff pressure, and `PB-ADAPTER-0` family closeout
  alignment.
- The implementation must wait until this `vNext+247` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_ADAPTER_0C_STARTER_LOCK`
- rationale:
  - released A now defines cleanroom task-visible material, artifact identity,
    visibility, access, and guardrails;
  - released B now defines local/reference probe plans, normalized
    observations, I/O artifact indexes, and filesystem side-effect
    observations;
  - C can bind those released rows into a case packet and readiness/handoff
    posture without running reconstruction or ProgramBench.
