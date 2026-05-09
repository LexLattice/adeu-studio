# Draft Stop-Gate Decision vNext+269

Status: pre-start scaffold decision for `PB-SINGLE-CASE-RUN-0-A`.

Authority layer: planning / starter scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This starter decision is scoped to `vNext+269` /
  `PB-SINGLE-CASE-RUN-0-A` only.
- It does not authorize implementation by itself until the starter bundle is
  accepted and committed.
- It selects the run-request, target-selection, execution-preflight,
  run-control-contract, and non-authority-guardrail seam only.
- It does not authorize worker dispatch, command execution, probe execution,
  candidate artifact capture, lifecycle projection, local outcome audit,
  remand or acceptance decision, retry authority, batch execution, official
  ProgramBench participation, official runner/evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  benchmark scoring, benchmark truth, pass rate, solve rate, success rate,
  baseline comparison, model ranking, leaderboard standing, official
  submission authority, retry-chain authority, future-family selection,
  product authorization, graph-memory authority, release authority, or
  recursive policy amendment.

## Evidence Source

- family selector:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v85.md`
- family architecture:
  - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_FAMILY_v0.md`
- family implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0_IMPLEMENTATION_MAPPING_v0.md`
- slice A implementation mapping:
  - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0A_IMPLEMENTATION_MAPPING_v0.md`
- starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS269.md`
- starter edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS269_EDGES.md`

## Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists | required before implementation | `pending` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS269.md` |
| Slice A stays preflight-only | required | `pending` | no worker dispatch, command execution, candidate capture, lifecycle projection, or outcome audit may ship |
| Exactly one target case lineage selected | required | `pending` | future A validator must reject multi-target requests |
| Matrix-member target origin is default | required | `pending` | target-origin route fields and route-specific refs required |
| Deferred/rejected matrix candidates are blocked | required | `pending` | future A reject fixture required |
| Direct adapter case route is exceptional | required | `pending` | future A validator requires exception posture and warning |
| Preflight has no dispatch authority | required | `pending` | `preflight_scope_posture = eligibility_review_only_no_dispatch` |
| B witness requirements are declared, not satisfied in A | required | `pending` | required B witness refs are schema fields only |
| Official ProgramBench and benchmark truth stay absent | required | `pending` | guardrail and reject fixtures required |
| Starter-bundle lint passes | required before implementation | `pending` | `make arc-start-check ARC=269` |

## Recommendation

- gate recommendation:
  - `SELECT_PB_SINGLE_CASE_RUN_0A_RUN_REQUEST_TARGET_SELECTION_AND_PREFLIGHT_ONLY`
- rationale:
  - `PB-SINGLE-CASE-RUN-0-A` is the narrowest safe first slice for the
    one-specimen local run family;
  - it prepares a single selected case-lineage target and preflight packet
    without dispatching a worker or capturing outcomes;
  - it keeps the default target route tied to matrix membership while
    allowing other routes only with explicit exception posture;
  - it leaves execution, capture, artifact materialization, lifecycle
    projection, outcome audit, remand, retry, batch execution, scoring,
    baseline comparison, model ranking, official participation, and
    future-family selection deferred.
