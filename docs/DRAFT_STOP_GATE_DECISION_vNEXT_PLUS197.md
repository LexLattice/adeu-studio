# Draft Stop-Gate Decision (Pre vNext+197)

This note records the pre-start scaffold decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`

Status: draft decision note (pre-start scaffold, April 26, 2026 UTC).

Authority layer: start-gate scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS197.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v197_pre_start_scaffold_only",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold for the bounded V71-A implementation lock. Final pass/fail evidence must replace this scaffold at closeout."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+197`.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md`.
- It does not claim implementation completion, settlement, ratification,
  candidate adoption, contained integration, product authorization, release
  authority, runtime permission, or dispatch widening.
- It records that `V71-A` is the next bounded starter candidate after the closed
  `V70` family.

## Pre-Start Scope Check

| Criterion | Required Posture | Pre-Start State |
|---|---|---|
| Target family / slice | `V71-A` only | selected by lock draft |
| Implementation package | `adeu_repo_description` only | planned |
| Starter surfaces | three `repo_*` request / authority / request-scope surfaces | planned |
| Ratification sources | explicit source rows, not prose memory | planned |
| V70-C substrate | summary and handoff rows consumed, not redefined | planned |
| Authority actor/source split | actor kind separate from grant source kind | planned |
| Request-scope boundary | request scope only, not amendment scope | planned |
| Final ratification | not performed by `V71-A` | forbidden |
| Downstream authority | no `V72+`, product, release, runtime, or dispatch | forbidden |

## Required Implementation Evidence At Closeout

The closeout decision must replace this scaffold with evidence for:

- typed models and schema exports for:
  - `repo_candidate_ratification_request@1`
  - `repo_ratification_authority_profile@1`
  - `repo_ratification_request_scope_boundary@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/repo_description/vnext_plus197/`
- schema mirrors under `spec/`
- package exports in `packages/adeu_repo_description`
- focused tests for the selected `V71-A` behavior
- `make check` during implementation
- closeout artifacts and `make arc-closeout-check ARC=197` after merge

## Pre-Start Decision

- gate posture:
  - `V71A_CANDIDATE_RATIFICATION_REQUEST_AUTHORITY_SCOPE_STARTER_LOCK_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - `V68`, `V69`, and `V70` are closed on `main` and supply the required map,
    candidate, and pre-ratification review substrate;
  - `V71-A` is narrow enough to implement as the first `V71` starter slice;
  - the lock defers final ratification records, settlement records,
    amendment-scope hardening, post-ratification handoff, contained integration,
    product projection, release authority, runtime permission, and dispatch
    widening.

