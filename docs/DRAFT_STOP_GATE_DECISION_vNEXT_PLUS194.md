# Draft Stop-Gate Decision (Pre vNext+194)

This note records the pre-start scaffold decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS194.md`

Status: draft decision note (pre-start scaffold, April 26, 2026 UTC).

Authority layer: start-gate scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS194.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v194_pre_start_scaffold_only",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold for the bounded V70-A implementation lock. Final pass/fail evidence must replace this scaffold at closeout."
}
```

## Decision Guardrail

- This draft is a pre-start scaffold for `vNext+194`.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS194.md`.
- It does not claim implementation completion, evidence settlement, candidate
  adoption, ratification, integration, product authorization, release authority,
  runtime permission, or dispatch widening.
- It records that `V70-A` is the next bounded starter candidate after the closed
  `V69` family and the reviewed `V70` planning/support bundle.

## Pre-Start Scope Check

| Criterion | Required Posture | Pre-Start State |
|---|---|---|
| Target family / slice | `V70-A` only | selected by lock draft |
| Implementation package | `adeu_repo_description` only | planned |
| Starter surfaces | three `repo_*` review-classification surfaces | planned |
| Claim registry | explicit claim rows required | planned |
| Evidence-source cardinality | singular `source_ref` on evidence-source rows | planned |
| Classification source refs | list-valued `evidence_source_refs` | planned |
| Missing / stale sources | explicit absence-posture evidence-source rows | planned |
| ODEU lane shape | sorted non-empty `odeu_lanes` | planned |
| Adversarial-review invariant | no required review marked not required | planned |
| Model-output comparison | adversarial review or conflict posture required | planned |
| Downstream authority | no `V70-B/C`, `V71+`, product, release, or dispatch | forbidden |

## Required Implementation Evidence At Closeout

The closeout decision must replace this scaffold with evidence for:

- typed models and schema exports for:
  - `repo_candidate_evidence_classification_record@1`
  - `repo_candidate_evidence_source_index@1`
  - `repo_candidate_review_boundary_guardrail@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/repo_description/vnext_plus194/`
- schema mirrors under `spec/`
- package exports in `packages/adeu_repo_description`
- focused tests for the selected `V70-A` behavior
- `make check` during implementation
- closeout artifacts and `make arc-closeout-check ARC=194` after merge

## Pre-Start Decision

- gate posture:
  - `V70A_STARTER_LOCK_READY_FOR_IMPLEMENTATION_REVIEW`
- rationale:
  - the `V70` family has one family-level selector, reviewed architecture, and
    A/B/C support specs;
  - `V70-A` is narrow enough to implement as the first slice;
  - the lock defers adversarial matrix, conflict relation register, review gap
    scan, synthesis, handoff, ratification, integration, product projection,
    release authority, and dispatch widening.

