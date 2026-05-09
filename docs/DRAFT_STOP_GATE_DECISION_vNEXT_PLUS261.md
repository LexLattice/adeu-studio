# Draft Stop-Gate Decision vNext+261

Status: pre-start decision scaffold for `PB-MATRIX-0-B`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS261.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+261` / `PB-MATRIX-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS261.md`.
- It does not authorize matrix summary, post-matrix handoff, family closeout,
  local case execution, batch command execution, candidate materialization,
  official ProgramBench participation, official task execution, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, pass rate,
  solve rate, success rate, model ranking, leaderboard standing, official
  submission authority, second retry authority, retry-chain authority,
  future-family selection, product authorization, graph-memory authority,
  release authority, or recursive policy amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-MATRIX-0-B` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS261.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS261_EDGES.md` |
| Prior slice `PB-MATRIX-0-A` is closed | required | pending | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS260.md` |
| Selected B record shapes are bounded | required | pending | result projection, observation ledger, coverage register, contamination register |
| Projections remain derived local views | required | pending | implementation validators and fixtures |
| Coverage remains local-only | required | pending | implementation validators and fixtures |
| Contamination fails closed without leaking forbidden detail | required | pending | implementation validators and fixtures |
| Matrix scoring and model ranking remain absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=261` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-MATRIX-0-B`;
- merge commit and merged-at timestamp;
- focused `PB-MATRIX-0-B` pytest;
- `make check`;
- docs/artifacts-only closeout verification for this closeout bundle;
- deterministic closeout artifacts for `vNext+261`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS261_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=261
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-MATRIX-0-B` can be considered closed.
