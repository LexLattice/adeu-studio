# Draft Stop-Gate Decision vNext+277

Status: pre-start scaffold for `OTB-0-C`.

Authority layer: planning scaffold.

This note records the planned closeout decision shape for the `vNext+277`
starter slice. It is not closeout evidence, does not claim the slice has
shipped, and must be updated after implementation and verification before it can
become post-closeout decision evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS277.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start scaffold is scoped to `vNext+277` / `OTB-0-C` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS277.md`.
- It does not authorize semantic adjudication, clean product truth claims, gate
  execution, probe generation, probe execution, worker dispatch, implementation
  authority, product behavior claims, official-eval authority, ProgramBench
  integration, future-family selection, release authority, or recursive policy
  amendment.
- This document must not be treated as post-closeout evidence until the
  implementation PR has merged and deterministic closeout artifacts exist.

## Planned Evidence Source

The post-closeout version of this decision should record:

- merged implementation PR;
- merge commit;
- implementation commits integrated by the merge;
- focused `OTB-0-C` pytest;
- full transition-broker pytest;
- transition-broker schema export pytest;
- `make lint`;
- `make check` or an explicitly justified full-gate escalation;
- docs/artifacts-only closeout verification with `make arc-closeout-check ARC=277`;
- deterministic closeout artifacts:
  - `artifacts/quality_dashboard_v277_closeout.json`;
  - `artifacts/stop_gate/metrics_v277_closeout.json`;
  - `artifacts/stop_gate/report_v277_closeout.md`;
  - metric-key continuity evidence input;
  - runtime observability evidence input;
  - `OTB-0-C` closeout evidence input;
  - committed runtime event-stream witness.

## Planned Exit-Criteria Check

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `OTB-0-C` merged on `main` | required | implementation PR and merge commit |
| Implementation stays in the transition-broker lane | required | package rooted at `packages/adeu_transition_broker` |
| Selected C surfaces ship | required | four record shapes from the lock |
| Released A/B records are consumed | required | C APIs accept A/B reports and reject missing required inputs |
| Score movement is not bridge proof | required | attribution fixtures reject score-as-proof |
| Official/postmortem pressure cannot be clean first-pass evidence | required | evidence-boundary fixtures |
| Earliest unproven bridge dominates attribution | required | dominance fixture |
| Stale phase objects are invalidated | required | object/contract/evidence/obligation/substrate/topology invalidation fixtures |
| Integration handoff is constrained | required | handoff forbidden-authority fixture |
| Family closeout cannot overclaim accepted surfaces | required | closeout alignment fixture |
| C does not execute plans or dispatch workers | required | non-authority fixtures |
| Canonical output hashing is stable | required | shuffled input fixture |
| Stop-gate schema-family continuity retained | required | closeout metrics |
| Stop-gate metric-key continuity retained | required | closeout evidence input |

## Pre-Start Recommendation

- gate decision:
  - `GO_OTB_0C_STARTER_IMPLEMENTATION_AFTER_BUNDLE_ACCEPTANCE`
- rationale:
  - `vNext+277` is scoped to one existing deterministic package and four
    C-level record surfaces;
  - the slice consumes released A/B substrate plus run-delta inputs and emits
    pressure-only attribution, stale-object invalidation, constrained handoff,
    and family closeout alignment;
  - execution, worker dispatch, implementation authority, clean product truth,
    official-eval authority, and future-family selection remain explicitly out
    of scope.
