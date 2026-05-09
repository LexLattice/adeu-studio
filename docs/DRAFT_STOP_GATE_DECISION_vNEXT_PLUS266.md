# Draft Stop-Gate Decision vNext+266

Status: pre-start decision scaffold for `PB-MATRIX-INCLUSION-0-A`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS266.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+266` /
  `PB-MATRIX-INCLUSION-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS266.md`.
- It does not authorize matrix amendment plans, case delta manifests,
  comparability delta reviews, contamination delta reviews, inclusion
  decision records, matrix revision registrations, readiness summaries,
  post-inclusion handoffs, family closeout, result projection, local case
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
| Starter lock exists for `PB-MATRIX-INCLUSION-0-A` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS266.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS266_EDGES.md` |
| Prior family `PB-CASE-EXPANSION-0` is closed | required | pending | `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_FAMILY_CLOSEOUT_v0.md` |
| Selected A record shapes are bounded | required | pending | request, candidate intake, eligibility review, control contract, and guardrail |
| Matrix baseline/revision identity is hash-bound | required | pending | implementation validators and fixtures |
| Candidate rows preserve lineage/probe/oracle/contamination identity | required | pending | implementation validators and fixtures |
| Dedupe against existing matrix membership is explicit | required | pending | implementation validators and fixtures |
| Inclusion remains non-representative and non-scoring | required | pending | implementation validators and fixtures |
| Execution/projection/scoring/ranking authority remains absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=266` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-MATRIX-INCLUSION-0-A`;
- merge commit and merged-at timestamp;
- focused `PB-MATRIX-INCLUSION-0-A` pytest;
- `make check`;
- docs/artifacts-only closeout verification for the closeout bundle;
- deterministic closeout artifacts for `vNext+266`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS266_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=266
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-MATRIX-INCLUSION-0-A` can be considered closed.
