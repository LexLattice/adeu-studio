# Draft Stop-Gate Decision vNext+271

Status: pre-start scaffold decision for `PB-SINGLE-CASE-RUN-0-C`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS271.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+271` /
  `PB-SINGLE-CASE-RUN-0-C` only.
- It does not authorize implementation by itself until the starter bundle is
  accepted and committed.
- It selects local outcome audit, observation summary, remand/acceptance
  decision, pressure-only handoff, and family closeout alignment.
- It does not authorize new worker dispatch, additional execution specimens,
  command execution, candidate artifact materialization, official ProgramBench
  participation, official runner/evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, benchmark scoring, benchmark
  truth, pass rate, solve rate, success rate, baseline comparison, model
  ranking, leaderboard standing, official submission authority, retry
  authority, batch execution, future-family selection, product authorization,
  graph-memory authority, release authority, or recursive policy amendment.

## Evidence Source

- family selector:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v85.md`
- family architecture:
  - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_FAMILY_v0.md`
- family implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0_IMPLEMENTATION_MAPPING_v0.md`
- slice C implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0C_IMPLEMENTATION_MAPPING_v0.md`
- released slice A closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md`
- released slice B closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS270.md`
- starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS271.md`
- starter edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS271_EDGES.md`

## Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists | required before implementation | `pending` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS271.md` |
| Slice C consumes released A/B refs | required | `pending` | future C validator must require released request, target, dispatch, trace, probe, capture, and projection refs |
| Local acceptance is strict | required | `pending` | no contamination, sandbox, lifecycle, output, artifact, probe, stdout/stderr, exit-code, or filesystem blockers |
| Candidate artifact capture is required | required | `pending` | artifact capture must exist and remain inside released write scope |
| Lifecycle projection is honored | required | `pending` | C acceptance must require valid B lifecycle projection |
| Observation summary is local-only | required | `pending` | soft benchmark, ranking, baseline, and hidden-test language rejected |
| Remand pressure is not retry authority | required | `pending` | remand decision posture must deny retry dispatch and future-family selection |
| Family closeout aligns A/B/C | required | `pending` | closeout alignment rows must list slices A, B, and C only |
| Starter-bundle lint passes | required before implementation | `pending` | `make arc-start-check ARC=271` |

## Recommendation

- gate recommendation:
  - `SELECT_PB_SINGLE_CASE_RUN_0C_LOCAL_OUTCOME_AUDIT_AND_FAMILY_CLOSEOUT`
- rationale:
  - `PB-SINGLE-CASE-RUN-0-B` closed the one-specimen capture/projection seam
    without local outcome authority;
  - `PB-SINGLE-CASE-RUN-0-C` is the next bounded seam because it classifies the
    captured specimen under declared local probe/oracle boundaries, summarizes
    observations, records pressure-only remand/acceptance posture, and closes
    only this family;
  - retry authority, batch execution, benchmark scoring, baseline comparison,
    model ranking, official participation, hidden-test equivalence, and
    future-family selection remain absent.
