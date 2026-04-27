# Draft Stop-Gate Decision (Pre vNext+204)

This note records the pre-start scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS204.md`

Status: pre-start scaffold decision note (April 27, 2026 UTC).

Authority layer: pre-start scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS204.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v204_pre_start_scaffold_only",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold markers must be superseded by post-closeout evidence and final decision values before vNext+204 is considered closed."
}
```

## Decision Guardrail

- This draft records `vNext+204` starter intent only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS204.md`.
- This note does not authorize `V73-C` self-improvement ledger rows,
  promotion / demotion recommendations, `V74` operator/product projection,
  `V75` dispatch, runtime permission, release authority, or external contest
  participation.
- Canonical `V73-B` shipment, if implemented, should be carried by bounded
  `adeu_repo_description` candidate outcome observation, outcome regression,
  and tool-fitness drift models, validators, schema exports, deterministic
  `vnext_plus204` reference and reject fixtures, and canonical closeout
  evidence under `artifacts/agent_harness/v204/`.

## Pre-Start Gate Criteria

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Starter lock exists | required | `pending` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS204.md` |
| Edge assessment exists | required | `pending` | `docs/ASSESSMENT_vNEXT_PLUS204_EDGES.md` |
| Family selector selects `V73-B` | required | `pending` | `docs/DRAFT_NEXT_ARC_OPTIONS_v63.md` |
| Implementation package remains repo-description only | required | `pending` | starter lock package scope |
| Selected starter surfaces are bounded to `V73-B` | required | `pending` | `repo_candidate_outcome_observation_record@1`, `repo_outcome_regression_register@1`, `repo_tool_fitness_drift_register@1` |
| Released `V73-A` entries are consumed | required | `pending` | future implementation validators |
| Benefit observation requires bounded evidence refs | required | `pending` | future implementation validators |
| No-regression posture requires checked coverage | required | `pending` | future implementation validators |
| Tool-fitness drift remains target-bound | required | `pending` | future implementation validators |
| Observation does not become recommendation or authority | required | `pending` | no `V73-C`, `V74`, or `V75` surfaces selected |
| Release, product, runtime, dispatch, and external contest authority remain forbidden | required | `pending` | future boundary validators |

## Planned Verification

Before closeout, the implementation PR should record:

- focused pytest for `V73-B` candidate outcome observation, regression, and
  tool-fitness drift models, validators, fixtures, and schema exports;
- `make check` for the Python lane before opening or updating the PR;
- post-merge docs/artifacts-only closeout verification with
  `make arc-closeout-check ARC=204`.

## Recommendation (Pre v204)

- gate decision:
  - `V73B_STARTER_READY_FOR_IMPLEMENTATION_AFTER_SCAFFOLD_ACCEPTANCE`
- rationale:
  - `v204` is narrowly scoped to outcome observation, regression, and
    tool-fitness drift substrate;
  - it consumes released `V73-A` entry, source-index, and guardrail material;
  - it emits only observation, regression, and tool-fitness record surfaces;
  - ledger, recommendation, product projection, runtime permission, release
    authority, dispatch, and external contest participation remain deferred.
