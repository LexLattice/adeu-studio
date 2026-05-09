# Draft Stop-Gate Decision vNext+270

Status: pre-start scaffold decision for `PB-SINGLE-CASE-RUN-0-B`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS270.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+270` /
  `PB-SINGLE-CASE-RUN-0-B` only.
- It does not authorize implementation by itself until the starter bundle is
  accepted and committed.
- It selects one local worker dispatch specimen, execution trace, local probe
  observation bundle, candidate artifact capture, and lifecycle projection.
- It does not authorize official ProgramBench participation, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, pass rate,
  solve rate, success rate, baseline comparison, model ranking, leaderboard
  standing, official submission authority, retry authority, batch execution,
  local outcome audit, remand or acceptance decision, future-family selection,
  product authorization, graph-memory authority, release authority, or
  recursive policy amendment.

## Evidence Source

- family selector:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v85.md`
- family architecture:
  - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_FAMILY_v0.md`
- family implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0_IMPLEMENTATION_MAPPING_v0.md`
- slice B implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0B_IMPLEMENTATION_MAPPING_v0.md`
- released slice A closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md`
- starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS270.md`
- starter edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS270_EDGES.md`

## Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists | required before implementation | `pending` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS270.md` |
| Slice B consumes released A refs | required | `pending` | future B validator must require A request, target, preflight, control, and guardrail refs |
| A preflight is not dispatch authority | required | `pending` | B dispatch authority ref required |
| Exactly one dispatch specimen exists | required | `pending` | `dispatch_specimen_index = 1`; duplicate dispatch rejected |
| Command rows are argv-shaped | required | `pending` | raw shell strings rejected unless later explicit authority exists |
| Sandbox witnesses are bound | required | `pending` | sandbox instance, attestation, network, Docker, secret, source lookup, decompilation, and write-scope witnesses required |
| Candidate artifact capture is screened | required | `pending` | forbidden-content screen must pass before capture validates |
| Lifecycle projection is not benchmark truth | required | `pending` | projection posture required |
| Official ProgramBench and benchmark scoring stay absent | required | `pending` | guardrails and reject fixtures required |
| Starter-bundle lint passes | required before implementation | `pending` | `make arc-start-check ARC=270` |

## Recommendation

- gate recommendation:
  - `SELECT_PB_SINGLE_CASE_RUN_0B_ONE_LOCAL_EXECUTION_SPECIMEN_CAPTURE`
- rationale:
  - `PB-SINGLE-CASE-RUN-0-A` closed the single-case target and preflight seam
    without dispatch authority;
  - `PB-SINGLE-CASE-RUN-0-B` is the next bounded action-adjacent seam because
    it records one local specimen under those released A controls;
  - it must bind dispatch to a B lock, require sandbox/tool/write-scope
    witnesses, keep command rows argv-shaped, screen output before artifact
    capture, and project lifecycle evidence without minting benchmark truth;
  - outcome audit, remand/acceptance, retry authority, batch execution,
    scoring, baseline comparison, model ranking, official participation, and
    future-family selection remain deferred.
