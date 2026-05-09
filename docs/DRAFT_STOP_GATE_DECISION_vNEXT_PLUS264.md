# Draft Stop-Gate Decision vNext+264

Status: pre-start decision scaffold for `PB-CASE-EXPANSION-0-B`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS264.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+264` / `PB-CASE-EXPANSION-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS264.md`.
- It does not authorize local case lineage registrations, readiness
  summaries, matrix candidate handoffs, family closeout, local case
  execution, probe execution, batch command execution, candidate
  materialization, official ProgramBench participation, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, baseline
  comparison, pass rate, solve rate, success rate, model ranking,
  leaderboard standing, official submission authority, second retry
  authority, retry-chain authority, future-family selection, product
  authorization, graph-memory authority, release authority, or recursive
  policy amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-CASE-EXPANSION-0-B` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS264.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS264_EDGES.md` |
| Prior slice `PB-CASE-EXPANSION-0-A` is closed | required | pending | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS263.md` |
| Selected B record shapes are bounded | required | pending | blueprint, evidence pack, probe contract, oracle boundary, and contamination screen |
| Behavior obligation evidence binding is explicit | required | pending | implementation validators and fixtures |
| Probe contracts remain argv-shaped and non-executing | required | pending | implementation validators and fixtures |
| Oracle boundaries remain local-only, not task truth | required | pending | implementation validators and fixtures |
| Contamination screens fail closed | required | pending | implementation validators and fixtures |
| Execution/scoring/ranking authority remains absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=264` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-CASE-EXPANSION-0-B`;
- merge commit and merged-at timestamp;
- focused `PB-CASE-EXPANSION-0-B` pytest;
- `make check`;
- docs/artifacts-only closeout verification for this closeout bundle;
- deterministic closeout artifacts for `vNext+264`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS264_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=264
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-CASE-EXPANSION-0-B` can be considered closed.
