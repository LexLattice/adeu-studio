# Draft Stop-Gate Decision (Pre vNext+195)

This note records the pre-start scaffold decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS195.md`

Status: draft decision note (pre-start scaffold, April 26, 2026 UTC).

Authority layer: start-gate scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS195.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v195_pre_start_scaffold_only",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold for the bounded V70-B implementation lock. Final pass/fail evidence must replace this scaffold at closeout."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+195`.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS195.md`.
- It does not claim implementation completion, evidence settlement, conflict
  resolution, candidate adoption, ratification, integration, product
  authorization, release authority, runtime permission, or dispatch widening.
- It records that `V70-B` is the next bounded starter candidate after the closed
  `V70-A` slice inside the already selected `V70` family.

## Pre-Start Scope Check

| Criterion | Required Posture | Pre-Start State |
|---|---|---|
| Target family / slice | `V70-B` only | selected by lock draft |
| Implementation package | `adeu_repo_description` only | planned |
| Starter surfaces | three `repo_*` adversarial/relation/gap surfaces | planned |
| V70-A substrate | classification rows consumed, not redefined | planned |
| Adversarial review matrix | classification-bound rows only | planned |
| Relation register | conflict and complementarity visible | planned |
| Gap scan | missing review/counterevidence/authority gaps explicit | planned |
| Conflict settlement | not performed by `V70-B` | forbidden |
| Downstream authority | no `V70-C`, `V71+`, product, release, or dispatch | forbidden |

## Required Implementation Evidence At Closeout

The closeout decision must replace this scaffold with evidence for:

- typed models and schema exports for:
  - `repo_candidate_adversarial_review_matrix@1`
  - `repo_candidate_review_conflict_register@1`
  - `repo_candidate_review_gap_scan@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/repo_description/vnext_plus195/`
- schema mirrors under `spec/`
- package exports in `packages/adeu_repo_description`
- focused tests for the selected `V70-B` behavior
- `make check` during implementation
- closeout artifacts and `make arc-closeout-check ARC=195` after merge

## Pre-Start Decision

- gate posture:
  - `V70B_ADVERSARIAL_REVIEW_GAP_SCAN_STARTER_LOCK_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - `V70-A` is closed on `main` and supplies the classification substrate;
  - `V70-B` is narrow enough to implement as the second slice;
  - the lock defers synthesis, pre-ratification handoff, ratification,
    integration, product projection, release authority, and dispatch widening.
