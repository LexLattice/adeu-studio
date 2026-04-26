# Draft Stop-Gate Decision (Pre vNext+198)

This note records the pre-start scaffold decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS198.md`

Status: draft decision note (pre-start scaffold, April 26, 2026 UTC).

Authority layer: start-gate scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS198.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v198_pre_start_scaffold_only",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold for the bounded V71-B implementation lock. Final pass/fail evidence must replace this scaffold at closeout."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+198`.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS198.md`.
- It does not claim implementation completion, candidate adoption,
  amendment-scope authority, post-ratification handoff, contained integration,
  product authorization, release authority, runtime permission, or dispatch
  widening.
- It records that `V71-B` is the next bounded starter candidate after closed
  `V71-A`.

## Pre-Start Scope Check

| Criterion | Required Posture | Pre-Start State |
|---|---|---|
| Target family / slice | `V71-B` only | selected by lock draft |
| Implementation package | `adeu_repo_description` only | planned |
| Starter surfaces | three `repo_*` ratification / settlement / dissent surfaces | planned |
| V71-A substrate | request, authority-profile, and request-scope rows consumed, not redefined | planned |
| Decision/routing split | decision posture, horizon, and next review surface stay separate | planned |
| Authority horizon validation | ratifying profiles must allow exact horizon | planned |
| Dissent preservation | dissent rows preserved or searched-none-found posture explicit | planned |
| Amendment scope / handoff | not performed by `V71-B` | forbidden |
| Downstream authority | no `V72+`, product, release, runtime, or dispatch | forbidden |

## Required Implementation Evidence At Closeout

The closeout decision must replace this scaffold with evidence for:

- typed models and schema exports for:
  - `repo_candidate_ratification_record@1`
  - `repo_review_settlement_record@1`
  - `repo_ratification_dissent_register@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/repo_description/vnext_plus198/`
- schema mirrors under `spec/`
- package exports in `packages/adeu_repo_description`
- focused tests for the selected `V71-B` behavior
- `make check` during implementation
- closeout artifacts and `make arc-closeout-check ARC=198` after merge

## Pre-Start Decision

- gate posture:
  - `V71B_CANDIDATE_RATIFICATION_SETTLEMENT_DISSENT_STARTER_LOCK_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - `V71-A` is closed on `main` and supplies the required source-bound
    request, authority-profile, and request-scope substrate;
  - `V71-B` is narrow enough to implement as the second `V71` starter slice;
  - the lock defers amendment-scope hardening, post-ratification handoff,
    contained integration, product projection, release authority, runtime
    permission, and dispatch widening.
