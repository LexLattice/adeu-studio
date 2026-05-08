# Draft Stop-Gate Decision vNext+256

Status: pre-start scaffold decision for `PB-TRIAL-0-C`.

Authority layer: planning / pre-lock scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS256.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold decision is scoped to `vNext+256` / `PB-TRIAL-0-C` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS256.md`.
- It does not authorize retry dispatch authority, multi-attempt comparison,
  official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, original source lookup,
  decompilation, internet lookup inside ProgramBench tasks, external
  repository lookup, benchmark submission, benchmark scoring, benchmark truth,
  model ranking, generated official submissions, official submission
  authority, unbounded command execution, target mutation outside released
  local artifacts, runtime transition, product authorization, graph-memory
  authority, recursive policy amendment, or future-family selection.

## Pre-Start Decision

Recommended scaffold decision:

- gate decision:
  - `PB_TRIAL_0C_STARTER_READY_FOR_IMPLEMENTATION_LOCK_REVIEW`
- rationale:
  - `PB-TRIAL-0-B` has closed on `main` as the local-dispatch specimen and
    lifecycle-projection seam;
  - `PB-TRIAL-0-C` is the correct next slice because it audits the single local
    trial outcome, summarizes the observation without comparison or benchmark
    claims, records local remand pressure without retry authority, and closes
    only `PB-TRIAL-0`;
  - the starter hardens the major interpretation edge by requiring released
    A/B refs, local-only evidence, candidate snapshot/write-scope closure,
    lifecycle projection validation, non-comparative observation summaries,
    and local-only remand source kinds;
  - retry authority, official ProgramBench participation, hidden-test
    equivalence, benchmark scoring, model ranking, official submissions, and
    future-family selection remain unselected.

## Required Exit Criteria For Later Closeout

The later closeout decision should require evidence that:

- `PB-TRIAL-0-C` shipped only outcome audit, observation summary, remand
  decision, and family closeout alignment shapes;
- released `PB-TRIAL-0-A/B` refs were required before validation;
- outcome audits could not exist without one trial docket, runbook, readiness
  review, dispatch record, execution capture, candidate snapshot, and
  lifecycle projection;
- local acceptance required no carried blockers, no sandbox violation, no
  output capture gap, no lifecycle projection gap, no hidden-test equivalence
  posture, and no official submission posture;
- local acceptance required a candidate snapshot inside released write scope;
- local acceptance required lifecycle projection validation against released
  `PB-ATTEMPT-0` validator bindings;
- observation summaries stayed single-trial-only and rejected comparative
  model, retry, benchmark, leaderboard, or multi-attempt language;
- remand decisions cited only local trial/attempt/workbench evidence sources;
- remand decisions could not cite hidden tests, official evaluator output,
  original source, decompilation, internet lookup, or external repository
  lookup;
- remand decisions could not become retry authority;
- family closeout alignment closed exactly `PB-TRIAL-0-A`, `PB-TRIAL-0-B`, and
  `PB-TRIAL-0-C`;
- no official benchmark authority, retry authority, model ranking, benchmark
  truth, official submission authority, or future-family selection shipped.

## Recommended Verification

- docs-only starter bundle:
  - `make arc-start-check ARC=256`
- later implementation PR:
  - focused `PB-TRIAL-0-C` pytest
  - `make check`
