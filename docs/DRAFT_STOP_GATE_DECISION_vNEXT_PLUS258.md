# Draft Stop-Gate Decision vNext+258

Status: pre-start scaffold decision for `PB-RETRY-0-B`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS258.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+258` / `PB-RETRY-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md`.
- It does not authorize retry outcome audit, retry delta observation summary,
  remand settlement, second retry authority, multi-attempt comparison,
  official ProgramBench participation, official task execution, official
  runner integration, official evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, original source lookup,
  decompilation, internet lookup inside ProgramBench tasks, external
  repository lookup, benchmark submission, benchmark scoring, benchmark truth,
  model ranking, generated official submissions, official submission
  authority, unbounded command execution, target mutation outside released
  local sandbox/write scope, runtime transition outside the local retry
  specimen, product authorization, graph-memory authority, recursive policy
  amendment, or future-family selection.

## Pre-Start Evidence Source

- family selector:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v81.md`
- architecture:
  - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md`
- implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0A_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0B_IMPLEMENTATION_MAPPING_v0.md`
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0C_IMPLEMENTATION_MAPPING_v0.md`
- prerequisite slice closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS257.md`
  - `docs/ASSESSMENT_vNEXT_PLUS257_EDGES.md`

## Entry-Criteria Check

| Criterion | Required State | Current Pre-Start State |
|---|---|---|
| Family selector exists | `PB-RETRY-0` selected as current family | draft selector created |
| Slice A closed | `PB-RETRY-0-A` complete on `main` | closeout drafted |
| Slice B selected | `PB-RETRY-0-B` selected as next slice candidate | selector continuation posture recorded |
| Starter lock exists | `LOCKED_CONTINUATION_vNEXT_PLUS258.md` | created |
| Edge assessment exists | `ASSESSMENT_vNEXT_PLUS258_EDGES.md` | created |
| Dispatch authority is explicit | B lock authority required; A eligibility is insufficient | locked |
| Retry cardinality is bounded | exactly one retry dispatch specimen per retry request | locked |
| Cleanroom continuity is preserved | A scope hashes and sandbox boundary remain binding | locked |
| Candidate delta snapshot is screened | snapshot blocked unless forbidden-content screen passes | locked |
| Future slice deferred | C outcome/settlement artifacts absent from B | locked |

## Required Start Gate

Before implementation starts, the docs-only starter bundle should pass:

```text
make arc-start-check ARC=258
```

During implementation, the future PR should run focused `PB-RETRY-0-B` tests
and `make check` before opening a ready-for-review PR.

## Recommendation

- gate decision:
  - `PB_RETRY_0B_STARTER_READY_FOR_REVIEW`
- rationale:
  - `PB-RETRY-0-B` is the next bounded execution-adjacent slice;
  - it records one retry dispatch specimen, retry execution capture,
    candidate delta snapshot, lifecycle projection, and sandbox application
    trace under released A retry-intake law;
  - it closes the key pre-start hardening before implementation:
    - dispatch requires B-lock authority;
    - one retry request produces at most one dispatch specimen;
    - retry execution remains local cleanroom evidence only;
    - candidate delta snapshotting requires passed forbidden-content screening;
    - sandbox traces must carry witness refs;
    - slice B emits no retry outcome audit, remand settlement, second retry
      authority, benchmark truth, model ranking, or future-family selection.
