# Draft Stop-Gate Decision (Pre vNext+210)

This note records the pre-start gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS210.md`

Status: draft decision note (pre-start scaffold, May 1, 2026 UTC).

Authority layer: planning / pre-start scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS210.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold only; final closeout evidence must replace this state after implementation merges."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for the bounded `V75-B` slice only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS210.md`.
- It does not authorize `V75-C`, worker assignment, command execution, runtime
  permission, product authorization, external contest participation, PR
  creation, commit, merge, release, benchmark truth, global model selection,
  living-memory authority, or recursive policy amendment.
- Canonical `V75-B` shipment, if implemented, must be carried by bounded
  `adeu_repo_description` worker role capacity profile, multi-worker
  assignment plan, worker IO contract, worker tool-applicability matrix, and
  dispatch exception register models, validators, schema exports,
  deterministic `vnext_plus210` reference and reject fixtures, and closeout
  evidence.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence Needed |
|---|---|---|---|
| `V75-B` implementation stays in repo-description lane | required | pending | implementation package list |
| Selected worker planning starter surfaces ship | required | pending | five `repo_*` V75-B surfaces |
| Released `V75-A` request / source / guardrail substrate is consumed | required | pending | reference fixture source refs |
| Assignment plans remain non-executing | required | pending | model validator and reject fixture |
| Role profiles cannot become permission grants | required | pending | role-as-permission reject fixture |
| Worker IO output remains non-truth | required | pending | output-as-truth reject fixture |
| Tool applicability remains target-bound and not tool-run permission | required | pending | tool-global-scope reject fixture |
| Upstream exceptions and later-authority blockers remain visible | required | pending | exception register fixture |
| External branch worker pressure remains blocked without `V43` source | required | pending | external-branch reject fixture |
| `V75-C` and runtime/product/release/external execution remain deferred | required | pending | closeout evidence |

## Recommended Local Gate

The implementation PR should run `make check` before opening or updating the PR.

For this docs-only starter bundle, the relevant pre-start verification is:

- `make arc-start-check ARC=210`

## Recommendation (Pre v210)

- gate decision:
  - `V75B_WORKER_ORCHESTRATION_PLANNING_STARTER_READY_FOR_IMPLEMENTATION`
- rationale:
  - `vNext+210` is scoped to the second bounded `V75-B` starter seam;
  - the selected surfaces are worker role capacity profile, multi-worker
    assignment plan, worker IO contract, worker tool-applicability matrix, and
    dispatch exception register only;
  - released `V75-A` dispatch-review substrate is the required source basis;
  - no worker assignment, command execution, runtime permission, product
    authorization, external contest participation, PR / commit / merge /
    release, benchmark truth, model selection, living-memory authority, or
    recursive policy amendment is selected.
