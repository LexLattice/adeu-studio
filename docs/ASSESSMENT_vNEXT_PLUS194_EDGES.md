# Assessment vNext+194 Edges

Status: pre-lock edge assessment for `V70-A` (April 26, 2026 UTC).

Authority layer: pre-lock assessment only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS194_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Evidence Classification Could Become Ratification

- Risk:
  `V70-A` rows could be overread as truth, adoption, or ratified decision.
- Required containment:
  boundary guardrail rows must forbid truth verdict, candidate adoption,
  ratified decision, implementation task, product authorization, release
  authority, and dispatch authority.

### Edge 2: Claim References Could Float

- Risk:
  classification rows could point to `claim_ref` values whose meaning is only
  implied by prose.
- Required containment:
  explicit claim rows are required, and dangling `claim_ref` values must fail
  closed.

### Edge 3: Missing Evidence Could Become Source-Free Memory

- Risk:
  `source_missing_or_stale` or `insufficient_evidence` rows could preserve
  missing-source claims without a source object.
- Required containment:
  missing, stale, unavailable, generated-later, or not-uploaded sources must be
  represented through explicit evidence-source rows with source-presence posture.

### Edge 4: Evidence Source Cardinality Could Drift

- Risk:
  mixed `source_ref` / `source_refs` naming could make validators ambiguous.
- Required containment:
  evidence-source rows use singular `source_ref`; classification rows use
  list-valued `evidence_source_refs`.

### Edge 5: ODEU Pressure Could Be Flattened

- Risk:
  review rows could collapse multi-lane pressure into a vague mixed label.
- Required containment:
  review rows carry sorted unique non-empty `odeu_lanes`; a single-lane row
  still uses a one-item list.

### Edge 6: Adversarial Review Need Could Be Contradictory

- Risk:
  a row could say evidence requires adversarial review while also marking
  adversarial review as not required.
- Required containment:
  `requires_adversarial_review` paired with `not_required_for_this_claim` must
  be rejected.

### Edge 7: Model-Output Comparison Could Skip Adversarial Review

- Risk:
  model-output comparison candidates could be classified from one side only.
- Required containment:
  model-output comparison candidates require adversarial-review or conflict
  posture.

### Edge 8: V70-A Could Begin V70-B Or V70-C

- Risk:
  the starter slice could drift into adversarial matrix, conflict relation
  register, gap scan, synthesis, or pre-ratification handoff work.
- Required containment:
  `V70-A` ships only source index, claim registry, classification rows,
  boundary guardrails, schemas, validators, exports, and reference/reject
  fixtures.

### Edge 9: Product Wedge Could Become Product Authorization

- Risk:
  product pressure could be classified as a selected `V74` projection.
- Required containment:
  product pressure can be reviewed as candidate evidence / authority boundary
  only; product authorization remains forbidden.

### Edge 10: Handoff Language Could Select Later Families

- Risk:
  classification rows could imply `V71`, `V72`, `V74`, or `V75` selection.
- Required containment:
  `V70-A` may mark adversarial review need and boundary posture only. It does
  not emit `V70-C` handoff rows or select later families.

## Residual Edges

- `V70-B` must later add adversarial review matrix, relation register, and gap
  scan without resolving conflicts.
- `V70-C` must later summarize and hand off review-classified candidates without
  ratifying them.
- `V71` remains the first planned family that may perform ratification review.

## Pre-Lock Judgment

- `V70-A` is an appropriate bounded starter after the closed `V69` family.
- The slice should be implemented only as schema/model/validator/export and
  reference/reject fixture work in `adeu_repo_description`.
- The implementation must keep review classification separate from truth,
  adoption, ratification, integration, product authorization, release authority,
  runtime permission, and dispatch.

