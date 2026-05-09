# Draft Stop-Gate Decision vNext+267

Status: pre-start decision scaffold for `PB-MATRIX-INCLUSION-0-B`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS267.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+267` /
  `PB-MATRIX-INCLUSION-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS267.md`.
- It does not authorize matrix revision registration, revision readiness
  summaries, post-inclusion handoffs, family closeout, result projection,
  matrix summary, local case execution, probe execution, batch command
  execution, candidate materialization, official ProgramBench participation,
  official runner/evaluator integration, hidden-test handling, hidden-test
  inference, hidden-test equivalence, benchmark scoring, benchmark truth,
  baseline comparison, pass rate, solve rate, success rate, model ranking,
  leaderboard standing, official submission authority, second retry
  authority, retry-chain authority, future-family selection, product
  authorization, graph-memory authority, release authority, or recursive
  policy amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-MATRIX-INCLUSION-0-B` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS267.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS267_EDGES.md` |
| Prior slice `PB-MATRIX-INCLUSION-0-A` is closed | required | pending | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS266.md` |
| Selected B record shapes are bounded | required | pending | amendment plan, case delta manifest, comparability delta review, contamination delta review, and inclusion decision record |
| Released A rows are required | required | pending | implementation validators and fixtures |
| Delta manifest accounts for every A-eligible candidate | required | pending | implementation validators and fixtures |
| Inclusion decisions remain governance/accounting decisions | required | pending | implementation validators and fixtures |
| Contamination transfer by summary is rejected | required | pending | implementation validators and fixtures |
| Execution/projection/scoring/ranking authority remains absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=267` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-MATRIX-INCLUSION-0-B`;
- merge commit and merged-at timestamp;
- focused `PB-MATRIX-INCLUSION-0-B` pytest;
- `make check`;
- docs/artifacts-only closeout verification for the closeout bundle;
- deterministic closeout artifacts for `vNext+267`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS267_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=267
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-MATRIX-INCLUSION-0-B` can be considered closed.
