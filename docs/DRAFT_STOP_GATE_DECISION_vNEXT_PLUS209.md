# Draft Stop-Gate Decision (Pre vNext+209)

This note records the pre-start gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md`

Status: draft decision note (pre-start scaffold, May 1, 2026 UTC).

Authority layer: planning / pre-start scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS209.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold only; final closeout evidence must replace this state after implementation merges."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for the bounded `V75-A` slice only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md`.
- It does not authorize `V75-B`, `V75-C`, worker assignment, command execution,
  runtime permission, product authorization, external contest participation,
  PR creation, commit, merge, release, benchmark truth, global model selection,
  living-memory authority, or recursive policy amendment.
- Canonical `V75-A` shipment, if implemented, must be carried by bounded
  `adeu_repo_description` dispatch-review request, dispatch source index, and
  non-execution guardrail models, validators, schema exports, deterministic
  `vnext_plus209` reference and reject fixtures, and closeout evidence.

## Pre-Start Exit-Criteria Plan

| Criterion | Threshold | Current State | Evidence Needed |
|---|---|---|---|
| `V75-A` implementation stays in repo-description lane | required | pending | implementation package list |
| Selected dispatch-review starter surfaces ship | required | pending | `repo_dispatch_review_request@1`, `repo_dispatch_source_index@1`, `repo_dispatch_non_execution_guardrail@1` |
| Released `V74-C` visibility / workbench / handoff substrate is consumed | required | pending | reference fixture source refs |
| Support / roadmap sources cannot be sole eligibility sources | required | pending | reject fixture and validator |
| Carried upstream exceptions remain `V74-C` origin-bound | required | pending | request validator and reject fixture |
| Required later authority rows are row-shaped | required | pending | reference fixture and free-floating authority reject |
| Non-execution guardrails are non-empty | required | pending | guardrail validator and reject fixture |
| Worker assignment and command execution reject | required | pending | reject fixtures |
| Product, runtime, external, release, benchmark, model-selection, and recursive-policy laundering reject | required | pending | reject fixtures |
| `V75-B` and `V75-C` remain deferred | required | pending | closeout evidence |

## Recommended Local Gate

The implementation PR should run `make check` before opening or updating the PR.

For this docs-only starter bundle, the relevant pre-start verification is:

- `make arc-start-check ARC=209`

## Recommendation (Pre v209)

- gate decision:
  - `V75A_DISPATCH_REVIEW_STARTER_READY_FOR_IMPLEMENTATION_AFTER_REVIEW`
- rationale:
  - `vNext+209` is scoped to the first bounded `V75-A` starter seam;
  - the selected surfaces are source-bound dispatch-review request, dispatch
    source index, and non-execution guardrail only;
  - review patches have narrowed eligibility, upstream exceptions, and later
    authority rows before lock activation;
  - no dispatch execution, worker assignment, runtime, product, external,
    release, benchmark, model-selection, living-memory, or recursive-policy
    authority is selected.
