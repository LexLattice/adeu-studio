# Draft Stop-Gate Decision vNext+248

Status: pre-start decision scaffold for `PB-RECON-0-A`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS248.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold is scoped to `vNext+248` / `PB-RECON-0-A` only.
- It does not replace `docs/LOCKED_CONTINUATION_vNEXT_PLUS248.md`.
- It does not authorize worker dispatch, generated Python implementation,
  candidate submission artifacts, local command execution, probe execution,
  equivalence audits, official ProgramBench participation, official task
  execution, official runner integration, official evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, arbitrary command execution, target
  mutation, runtime transition, product authorization, graph-memory authority,
  recursive policy amendment, or future-family selection.

## Pre-Start Exit Criteria

| Criterion | Threshold | Pre-Start State |
|---|---|---|
| Family selected by selector | required | `PB-RECON-0` selected by `DRAFT_NEXT_ARC_OPTIONS_v78.md` |
| Prior family closeout present | required | `PB-ADAPTER-0` closed by `DRAFT_STOP_GATE_DECISION_vNEXT_PLUS247.md` and family closeout note |
| Slice-A lock present | required | `LOCKED_CONTINUATION_vNEXT_PLUS248.md` drafted |
| Slice scope is bounded | required | work order, worker-visible context packet, auditor-only exclusion manifest, sandbox policy, run budget, and guardrail only |
| Released case-packet substrate required | required | A rows must consume released case packet, readiness summary, handoff, and family closeout refs |
| Ready uncontaminated case packet required | required | blocked, contaminated, hidden-exposed, forbidden-exposed, or future-family-only case packets cannot become work orders |
| Worker context is worker-visible only | required | hidden, forbidden, postmortem-only, original-source, decompilation, external-repo, Docker-socket, host-secret, and excluded derived-summary refs cannot enter worker context |
| Exclusion manifest is auditor-only | required | hidden/forbidden/postmortem/excluded refs may be recorded for audit but not served to the worker |
| Sandbox policy is non-execution law | required | sandbox declares future witness requirements but grants no execution authority in A |
| Run budget is non-execution law | required | budgets constrain later work but do not authorize command execution or probe execution |
| Deferred B/C surfaces stay deferred | required | no candidate artifacts, run traces, probe logs, remand records, equivalence audits, summaries, handoffs, or family closeout rows |
| Official ProgramBench and benchmark truth stay absent | required | no official runner/evaluator, hidden tests, benchmark scores, model rankings, or official submissions |
| Starter bundle gate | required before implementation | `make arc-start-check ARC=248` |

## Initial Stop-Gate Posture

- `PB-RECON-0-A` is the logical first slice after the released
  `PB-ADAPTER-0` case-packet substrate.
- The starter lock is coherent if it remains limited to workbench boundary
  definition and does not dispatch a worker, generate code, execute commands,
  run probes, or score results.
- The implementation must wait until this `vNext+248` starter bundle is
  accepted.

## Recommendation

- pre-start decision:
  - `READY_TO_REVIEW_PB_RECON_0A_STARTER_LOCK`
- rationale:
  - released `PB-ADAPTER-0` now defines case-packet readiness, visibility,
    access, local probe observations, and handoff pressure;
  - `PB-RECON-0-A` can define the exact local workbench boundary for a later
    reconstruction worker without granting dispatch or execution authority;
  - the worker-visible context / auditor-only exclusion split closes the main
    leak risk before any implementation work begins.
