# Assessment vNext+198 Edges

Status: pre-lock edge assessment for `V71-B` (April 26, 2026 UTC).

Authority layer: pre-lock assessment only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS198_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Ratification Record Could Become Implementation Authority

- Risk:
  ratification records could be overread as permission to edit, integrate,
  merge, release, productize, run, or dispatch work.
- Required containment:
  `V71-B` may emit ratification / rejection / deferral, settlement, and dissent
  rows only; implementation and integration remain deferred to later locks.

### Edge 2: V71-A Requests Could Be Recreated In Parallel

- Risk:
  `V71-B` could mint its own request universe rather than consuming released
  `V71-A` rows.
- Required containment:
  ratification, settlement, and dissent rows must reference known `V71-A`
  request rows.

### Edge 3: Authority Profile Horizon Could Be Ignored

- Risk:
  an authority profile could be used to ratify a horizon it was not allowed to
  ratify.
- Required containment:
  every ratifying authority profile must include the exact ratification horizon
  carried by the ratification record.

### Edge 4: Outcome And Routing Could Collapse

- Risk:
  `ratified_for_v72` style wording could make ratification look like direct
  `V72` selection or implementation authorization.
- Required containment:
  `decision_posture`, `ratification_horizon`, and
  `allowed_next_review_surface` stay separate.

### Edge 5: Blocked Requests Could Be Ratified Without Settlement

- Risk:
  `requires_settlement_before_ratification` requests could be ratified without
  a settlement row.
- Required containment:
  blocked requests require settlement records or explicit deferral /
  carry-forward posture.

### Edge 6: Conflict And Complementarity Could Collapse

- Risk:
  complementary review relation could be treated as conflict, or conflict could
  be silently treated as settled.
- Required containment:
  relation kind remains first-class and unresolved blocking conflict cannot be
  treated as settled by default.

### Edge 7: Evidence Gaps Could Be Hidden

- Risk:
  unresolved gaps could be ratified away rather than carried forward.
- Required containment:
  unresolved blocking gaps require deferral, carry-forward, or review-required
  posture.

### Edge 8: Dissent Could Be Dropped

- Risk:
  partial settlement or unresolved blockers could omit dissent rows, or
  `no_dissent_recorded` could be used as proof of absence without search
  coverage.
- Required containment:
  dissent rows are required for partial / unresolved settlement postures, and
  `no_dissent_recorded` requires `searched_none_found` before it can mean no
  dissent was found.

### Edge 9: Product Wedge Could Be Ratified For Integration

- Risk:
  product-facing pressure could be ratified for `V72` integration review before
  the `V74` product/operator boundary exists.
- Required containment:
  product wedge candidates remain future-family routed and cannot be ratified
  for integration review in `V71-B`.

### Edge 10: V71-B Could Begin V71-C

- Risk:
  settlement and ratification records could start defining amendment scope or
  post-ratification handoff.
- Required containment:
  amendment-scope boundary and post-ratification handoff surfaces remain
  deferred to `V71-C`.

## Pre-Lock Judgment

- `V71-B` is an appropriate bounded second slice after closed `V71-A`.
- The slice should be implemented only as schema/model/validator/export and
  reference/reject fixture work in `adeu_repo_description`.
- The implementation must keep ratification records, settlement records, and
  dissent registers separate from amendment scope, contained integration,
  product authorization, release authority, runtime permission, and dispatch.
