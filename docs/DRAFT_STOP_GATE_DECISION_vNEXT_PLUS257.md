# Draft Stop-Gate Decision vNext+257

Status: pre-start scaffold decision for `PB-RETRY-0-A`.

Authority layer: planning / pre-start scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS257.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This pre-start decision is scoped to `vNext+257` / `PB-RETRY-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS257.md`.
- It does not authorize retry dispatch, command execution, retry candidate
  delta snapshotting, local retry execution capture, retry lifecycle
  projection, retry outcome audit, retry delta observation summary, remand
  settlement, second retry authority, multi-attempt comparison, official
  ProgramBench participation, official task execution, official runner
  integration, official evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, original source lookup,
  decompilation, internet lookup inside ProgramBench tasks, external
  repository lookup, benchmark submission, benchmark scoring, benchmark truth,
  model ranking, generated official submissions, official submission
  authority, unbounded command execution, target mutation outside released
  local artifacts, runtime transition, product authorization, graph-memory
  authority, recursive policy amendment, or future-family selection.

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
- prerequisite family closeout:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`

## Entry-Criteria Check

| Criterion | Required State | Current Pre-Start State |
|---|---|---|
| Family selector exists | `PB-RETRY-0` selected as next family | draft selector created |
| Slice A selected | `PB-RETRY-0-A` selected as first slice candidate | draft selector created |
| Starter lock exists | `LOCKED_CONTINUATION_vNEXT_PLUS257.md` | created |
| Edge assessment exists | `ASSESSMENT_vNEXT_PLUS257_EDGES.md` | created |
| Scope is non-executing | no retry dispatch or command execution | locked |
| Retry uniqueness is explicit | one eligible retry per trial remand decision | locked |
| Cleanroom continuity is explicit | unchanged evidence/tool/sandbox/write/network boundaries | locked |
| Remand source is local-only | no hidden/forbidden/evaluator/source rationale | locked |
| Future slices deferred | B/C artifacts absent from A | locked |

## Required Start Gate

Before implementation starts, the docs-only starter bundle should pass:

```text
make arc-start-check ARC=257
```

During implementation, the future PR should run focused `PB-RETRY-0-A` tests
and `make check` before opening a ready-for-review PR.

## Recommendation

- gate decision:
  - `PB_RETRY_0A_STARTER_READY_FOR_REVIEW`
- rationale:
  - `PB-RETRY-0-A` is the next bounded non-executing slice;
  - it records retry request, retry lineage registry, remand source index,
    eligibility review, scope contract, and non-authority guardrail only;
  - it closes the key review hardening before implementation:
    - remand pressure is not dispatch authority;
    - many "single" retries over the same remand are rejected;
    - retry rationale is local-only and content-shaped;
    - cleanroom boundaries are hash-bound and unchanged;
    - slice A emits no retry execution or outcome artifacts.
