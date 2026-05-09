# Draft Stop-Gate Decision vNext+268

Status: pre-start decision scaffold for `PB-MATRIX-INCLUSION-0-C`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS268.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+268` /
  `PB-MATRIX-INCLUSION-0-C` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS268.md`.
- It does not authorize local case execution, probe execution, batch command
  execution, candidate materialization, result projection, post-execution
  matrix summary, official ProgramBench participation, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, baseline
  comparison, pass rate, solve rate, success rate, model ranking, leaderboard
  standing, official submission authority, second retry authority,
  retry-chain authority, future-family selection, product authorization,
  graph-memory authority, release authority, or recursive policy amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-MATRIX-INCLUSION-0-C` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS268.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS268_EDGES.md` |
| Prior slices `PB-MATRIX-INCLUSION-0-A/B` are closed | required | pending | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS266.md`, `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS267.md` |
| Selected C record shapes are bounded | required | pending | revision registration, revision readiness summary, post-inclusion handoff, and family closeout alignment |
| Released B rows are required | required | pending | implementation validators and fixtures |
| Revision registration matches B decision | required | pending | implementation validators and fixtures |
| Revision counts remain inventory-only | required | pending | implementation validators and fixtures |
| Post-inclusion handoff remains pressure-only | required | pending | implementation validators and fixtures |
| Execution/projection/scoring/ranking authority remains absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=268` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-MATRIX-INCLUSION-0-C`;
- merge commit and merged-at timestamp;
- focused `PB-MATRIX-INCLUSION-0-C` pytest;
- `make check`;
- docs/artifacts-only closeout verification for the closeout bundle;
- deterministic closeout artifacts for `vNext+268`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS268_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=268
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-MATRIX-INCLUSION-0-C` can be considered closed.
