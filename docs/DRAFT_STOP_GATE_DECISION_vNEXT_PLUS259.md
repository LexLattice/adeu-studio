# Draft Stop-Gate Decision vNext+259

Status: pre-start decision scaffold for `PB-RETRY-0-C`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS259.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+259` / `PB-RETRY-0-C` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS259.md`.
- It does not authorize a second retry request, retry dispatch, command
  execution, candidate materialization, official ProgramBench participation,
  official runner/evaluator integration, hidden-test handling, hidden-test
  inference, hidden-test equivalence, benchmark scoring, benchmark truth,
  model ranking, official submission authority, future-family selection,
  product authorization, graph-memory authority, or recursive policy
  amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-RETRY-0-C` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS259.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS259_EDGES.md` |
| Prior slice `PB-RETRY-0-B` is closed | required | pending | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS258.md` |
| Selected C record shapes are bounded | required | pending | outcome audit, delta summary, remand settlement, family closeout alignment |
| Second retry authority remains absent | required | pending | implementation validators and fixtures |
| Same-lineage comparison stays local-only | required | pending | implementation validators and fixtures |
| Benchmark truth and model ranking stay absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=259` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-RETRY-0-C`;
- merge commit and merged-at timestamp;
- focused `PB-RETRY-0-C` pytest;
- `make check`;
- docs/artifacts-only closeout verification for this closeout bundle;
- deterministic closeout artifacts for `vNext+259`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS259_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=259
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-RETRY-0-C` can be considered closed.
