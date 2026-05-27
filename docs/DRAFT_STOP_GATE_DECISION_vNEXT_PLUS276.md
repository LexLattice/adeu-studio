# Draft Stop-Gate Decision vNext+276

Status: pre-start scaffold for `OTB-0-B`.

Authority layer: planning scaffold.

This note records the planned closeout decision shape for the `vNext+276`
starter slice. It is not closeout evidence, does not claim the slice has
shipped, and must be updated after implementation and verification before it can
become post-closeout decision evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS276.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start scaffold is scoped to `vNext+276` / `OTB-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS276.md`.
- It does not authorize gate execution, probe execution, worker dispatch,
  implementation authority, product behavior claims, official-eval authority,
  ProgramBench integration, future-family selection, release authority, or
  recursive policy amendment.
- This document must not be treated as post-closeout evidence until the
  implementation PR has merged and deterministic closeout artifacts exist.

## Planned Evidence Source

The post-closeout version of this decision should record:

- merged implementation PR;
- merge commit;
- implementation commits integrated by the merge;
- focused `OTB-0-B` pytest;
- full transition-broker pytest;
- transition-broker schema export pytest;
- `make lint`;
- `make check` or an explicitly justified full-gate escalation;
- docs/artifacts-only closeout verification with `make arc-closeout-check ARC=276`;
- deterministic closeout artifacts:
  - `artifacts/quality_dashboard_v276_closeout.json`;
  - `artifacts/stop_gate/metrics_v276_closeout.json`;
  - `artifacts/stop_gate/report_v276_closeout.md`;
  - metric-key continuity evidence input;
  - runtime observability evidence input;
  - `OTB-0-B` closeout evidence input;
  - committed runtime event-stream witness.

## Planned Exit-Criteria Check

| Criterion | Threshold | Planned Evidence |
|---|---|---|
| `OTB-0-B` merged on `main` | required | implementation PR and merge commit |
| Implementation stays in the transition-broker lane | required | package rooted at `packages/adeu_transition_broker` |
| Selected B surfaces ship | required | five record shapes from the lock |
| Released A validation reports are consumed | required | B APIs accept A reports and reject unresolved A diagnostics |
| Closure posture does not exceed weakest required transition | required | closure fixtures |
| Gate plans are plan-only | required | gate plan authority posture fixture |
| Worker baton contracts do not dispatch workers | required | baton non-dispatch fixture |
| Evidence posture plans remain plan-only | required | evidence posture authority fixture |
| Operationalization reports cannot imply execution | required | operationalization non-authority fixture |
| Representative-only rows cannot become gold/official ready | required | readiness downgrade fixture |
| Known-risk statement required for scoped readiness | required | scoped-risk fixture |
| Unknown validation report refs or stale hashes fail closed | required | hash/ref fixtures |
| B does not implement C surfaces | required | no delta/stale/handoff/family-closeout APIs |
| Canonical output hashing is stable | required | shuffled input fixture |
| Stop-gate schema-family continuity retained | required | closeout metrics |
| Stop-gate metric-key continuity retained | required | closeout evidence input |

## Pre-Start Recommendation

- gate decision:
  - `GO_OTB_0B_STARTER_IMPLEMENTATION_AFTER_BUNDLE_ACCEPTANCE`
- rationale:
  - `vNext+276` is scoped to one existing deterministic package and five
    B-level record surfaces;
  - the slice computes transition closure/readiness and emits plan-only gate,
    baton, evidence posture, and operationalization records over released
    A-level validation reports;
  - C-level delta attribution, stale-object invalidation, integration handoff,
    family closeout, execution, product authority, and future-family selection
    remain explicitly out of scope.
