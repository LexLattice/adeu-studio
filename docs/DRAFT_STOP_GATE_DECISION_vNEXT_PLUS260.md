# Draft Stop-Gate Decision vNext+260

Status: pre-start decision scaffold for `PB-MATRIX-0-A`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS260.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+260` / `PB-MATRIX-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS260.md`.
- It does not authorize per-case result projection, observation ledger,
  coverage register, contamination register, matrix summary, handoff,
  family closeout, official ProgramBench participation, official task
  execution, official runner/evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, benchmark scoring,
  benchmark truth, pass rate, solve rate, success rate, model ranking,
  leaderboard standing, official submission authority, batch execution,
  second retry authority, retry-chain authority, future-family selection,
  product authorization, graph-memory authority, release authority, or
  recursive policy amendment.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists for `PB-MATRIX-0-A` | required | pending | `docs/LOCKED_CONTINUATION_vNEXT_PLUS260.md` |
| Closeout decision scaffold exists | required | pending | this file |
| Edge assessment scaffold exists | required | pending | `docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md` |
| Prior family `PB-RETRY-0` is closed | required | pending | `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md` |
| Selected A record shapes are bounded | required | pending | request, inclusion manifest, eligibility review, control contract, guardrail |
| Case aggregation remains non-scoring | required | pending | implementation validators and fixtures |
| Matrix controls remain non-ranking | required | pending | implementation validators and fixtures |
| Batch execution remains absent | required | pending | implementation validators and fixtures |
| Docs-only starter gate passes | required | pending | `make arc-start-check ARC=260` |

## Planned Evidence Source

Future closeout should record:

- merged implementation PR for `PB-MATRIX-0-A`;
- merge commit and merged-at timestamp;
- focused `PB-MATRIX-0-A` pytest;
- `make check`;
- docs/artifacts-only closeout verification for this closeout bundle;
- deterministic closeout artifacts for `vNext+260`;
- closeout edge assessment in `docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md`.

## Recommendation

Proceed only after the starter bundle passes:

```text
make arc-start-check ARC=260
```

The future closeout decision must replace this scaffold with post-closeout
evidence before `PB-MATRIX-0-A` can be considered closed.
