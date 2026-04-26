# Assessment vNext+197 Edges

Status: pre-lock edge assessment for `V71-A` (April 26, 2026 UTC).

Authority layer: pre-lock assessment only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS197_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Ratification Request Could Become Ratification

- Risk:
  request rows could be overread as final ratification, rejection, or adoption.
- Required containment:
  `V71-A` may emit request, authority profile, and request-scope boundary rows
  only; final ratification outcomes belong to `V71-B`.

### Edge 2: Source Rows Could Collapse Into Prose Memory

- Risk:
  ratification requests could be reconstructed from planning prose, model
  preference, operator vibe, or uncommitted transcript.
- Required containment:
  every request, authority profile, and request-scope boundary must resolve
  through concrete ratification source rows or explicit absence rows.

### Edge 3: Authority Actor Could Be Confused With Authority Source

- Risk:
  `repo_lock`, support docs, tools, or transcripts could be treated as actors.
- Required containment:
  actor kind and authority grant source kind stay separate; non-human /
  non-maintainer sources default to review-only, advisory-only, evidence-only,
  or not-authorized posture unless explicitly granted.

### Edge 4: Model, Tool, Support, Or Transcript Could Self-Ratify

- Risk:
  model output, tool success, support docs, or transcript content could be
  laundered into ratification authority.
- Required containment:
  reject self-ratification, tool-pass-as-ratification, support-doc-as-authority,
  and transcript-as-truth / transcript-as-authority fixtures.

### Edge 5: Blocked Handoff Could Be Marked Eligible

- Risk:
  `blocked_by_conflict` or gap-bearing `V70-C` handoffs could become eligible
  ratification requests without settlement requirement.
- Required containment:
  blocked handoffs map to `requires_settlement_before_ratification` and carry a
  `settlement_required`, `evidence_required`, or `gating_blocker` review signal.

### Edge 6: Product Wedge Could Enter V71 Ratification

- Risk:
  product-facing pressure could be routed into `V71` ratification review and
  then overread as future product or integration permission.
- Required containment:
  product wedge / future-family handoff rows remain future-family deferrals and
  cannot become `V71` ratification requests.

### Edge 7: Request Scope Could Become Amendment Scope

- Risk:
  starter request-scope boundaries could be treated as `V71-C` amendment scope.
- Required containment:
  `repo_ratification_request_scope_boundary@1` bounds what a request may ask
  for only; amendment scope remains deferred to `V71-C`.

### Edge 8: Warning Signals Could Become Blockers Or Settlement

- Risk:
  warning-only review signals, gating blockers, settlement requirements, and
  evidence requirements could collapse into one generic review status.
- Required containment:
  `review_signal_posture` remains first-class and must not be silently repaired.

### Edge 9: V71-A Could Begin V71-B Or V71-C

- Risk:
  starter implementation could include ratification records, settlement records,
  dissent registers, amendment scope, or post-ratification handoff.
- Required containment:
  `V71-A` ships only request, authority profile, request-scope, schema,
  validator, export, and fixture work.

### Edge 10: V72 Or Later Authority Could Leak In

- Risk:
  request rows or scope rows could select implementation, contained integration,
  product projection, release authority, runtime permission, dispatch, or
  external contest participation.
- Required containment:
  downstream roles are forbidden in request-scope boundaries; later-family
  review remains deferred until its own lock.

## Pre-Lock Judgment

- `V71-A` is an appropriate bounded first slice after closed `V68`, `V69`, and
  `V70`.
- The slice should be implemented only as schema/model/validator/export and
  reference/reject fixture work in `adeu_repo_description`.
- The implementation must keep ratification requests, authority profiles, and
  request-scope boundaries separate from final ratification, settlement,
  amendment scope, contained integration, product authorization, release
  authority, runtime permission, and dispatch.

