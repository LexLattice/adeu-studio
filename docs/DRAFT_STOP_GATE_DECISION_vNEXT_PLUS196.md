# Draft Stop-Gate Decision (Pre vNext+196)

This note records the pre-start scaffold decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS196.md`

Status: draft decision note (pre-start scaffold, April 26, 2026 UTC).

Authority layer: start-gate scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS196.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v196_pre_start_scaffold_only",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold for the bounded V70-C implementation lock. Final pass/fail evidence must replace this scaffold at closeout."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+196`.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS196.md`.
- It does not claim implementation completion, evidence settlement, conflict
  resolution, candidate adoption, ratification, integration, product
  authorization, release authority, runtime permission, or dispatch widening.
- It records that `V70-C` is the next bounded starter candidate after the closed
  `V70-B` slice inside the already selected `V70` family.

## Pre-Start Scope Check

| Criterion | Required Posture | Pre-Start State |
|---|---|---|
| Target family / slice | `V70-C` only | selected by lock draft |
| Implementation package | `adeu_repo_description` only | planned |
| Starter surfaces | two `repo_*` summary/handoff surfaces | planned |
| V70-A substrate | classification rows consumed, not redefined | planned |
| V70-B substrate | adversarial/relation/gap rows consumed, not settled | planned |
| Summary posture | later-review classification only | planned |
| Pre-ratification handoff | request or defer later review only | planned |
| Ratification | not performed by `V70-C` | forbidden |
| Downstream authority | no `V71+`, product, release, or dispatch | forbidden |

## Required Implementation Evidence At Closeout

The closeout decision must replace this scaffold with evidence for:

- typed models and schema exports for:
  - `repo_candidate_review_classification_summary@1`
  - `repo_candidate_pre_ratification_handoff@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/repo_description/vnext_plus196/`
- schema mirrors under `spec/`
- package exports in `packages/adeu_repo_description`
- focused tests for the selected `V70-C` behavior
- `make check` during implementation
- closeout artifacts and `make arc-closeout-check ARC=196` after merge

## Pre-Start Decision

- gate posture:
  - `V70C_REVIEW_SUMMARY_PRE_RATIFICATION_HANDOFF_STARTER_LOCK_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - `V70-A` and `V70-B` are closed on `main` and supply the required review
    substrate;
  - `V70-C` is narrow enough to implement as the third and final `V70` slice;
  - the lock defers ratification, integration, product projection, release
    authority, runtime permission, and dispatch widening.
