# Draft Stop-Gate Decision vNext+245

Status: pre-start decision scaffold for `PB-ADAPTER-0-A`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS245.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+245` / `PB-ADAPTER-0-A` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS245.md`.
- It does not authorize official ProgramBench participation, official task
  execution, official runner integration, hidden-test handling, hidden-test
  inference, original source lookup, decompilation, internet lookup inside
  ProgramBench tasks, external repository lookup, benchmark submission,
  benchmark scoring, benchmark truth, model ranking, generated official
  submissions, probe execution, command execution, tool invocation, target
  mutation, runtime transition, product authorization, graph-memory authority,
  recursive policy amendment, or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-ADAPTER-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v77.md` |
| Slice-A lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS245.md` drafted |
| Slice scope is bounded | required | task intake, artifact manifest, visibility manifest, worker access contract, guardrail only |
| Forbidden evidence posture is fail-closed | required | hidden/forbidden sources cannot be worker-visible, inference refs, or derived summaries |
| Command/probe/submission authority absent | required | no command execution, probe execution, or submission generation authority in slice A |
| Later surfaces deferred | required | probe observations, case packets, readiness summaries, handoffs, official ProgramBench participation, and benchmark results deferred |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=245` |

## Recommendation

- gate decision:
  - `READY_TO_REVIEW_PB_ADAPTER_0A_STARTER_LOCK`
- rationale:
  - `PB-ADAPTER-0-A` is the narrow first slice needed after `PB-PY-0`;
  - it creates the cleanroom membrane before any active evidence creation:
    task intake, stable artifact identity, visibility law, worker access
    contract, and non-authority guardrail;
  - it keeps probe observation, reconstruction case packets, official
    benchmark participation, generated submissions, benchmark scores, and
    model ranking out of scope.

## Open Pre-Implementation Notes

- External review should check whether artifact identity fields are sufficient
  for later reproducible worker-visible context.
- External review should check whether derived-summary exposure rules are
  strict enough to block hidden/forbidden evidence laundering.
- External review should check whether slice A keeps command/probe authority
  absent rather than pre-authorizing slice B behavior.
