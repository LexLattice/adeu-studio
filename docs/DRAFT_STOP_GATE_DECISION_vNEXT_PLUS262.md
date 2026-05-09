# Draft Stop-Gate Decision vNext+262

Status: pre-start decision scaffold for `PB-MATRIX-0-C`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS262.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+262` / `PB-MATRIX-0-C` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS262.md`.
- It does not authorize local case execution, batch command execution,
  candidate materialization, official ProgramBench participation, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, pass rate,
  solve rate, success rate, model ranking, leaderboard standing, official
  submission authority, second retry authority, retry-chain authority,
  future-family selection, product authorization, graph-memory authority,
  release authority, or recursive policy amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-MATRIX-0-C` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS262.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS262_EDGES.md` |
| Prior slice `PB-MATRIX-0-B` is closed | required | pending | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS261.md` |
| Selected C record shapes are bounded | required | pending | matrix summary, post-matrix handoff, family closeout alignment |
| Summary remains local-only | required | pending | implementation validators and fixtures |
| Aggregate counts remain accounting-only | required | pending | implementation validators and fixtures |
| Handoff remains pressure-only and non-selecting | required | pending | implementation validators and fixtures |
| Family closeout closes only `PB-MATRIX-0` | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=262` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-MATRIX-0-C`;
- merge commit and merged-at timestamp;
- focused `PB-MATRIX-0-C` pytest;
- `make check`;
- docs/artifacts-only closeout verification for this closeout bundle;
- deterministic closeout artifacts for `vNext+262`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS262_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=262
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-MATRIX-0-C` can be considered closed.
