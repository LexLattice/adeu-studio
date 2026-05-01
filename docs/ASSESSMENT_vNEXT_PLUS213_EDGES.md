# Assessment vNext+213 Edges

Status: planning-edge assessment for `V76-B`.

Authority layer: pre-lock assessment, not closeout evidence.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS213_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Arbiter Authority Could Become Truth Authority

- Risk:
  an authority profile could be overread as permission for an arbiter, model,
  tool, support doc, or transcript to declare truth.
- Response:
  split actor kind from grant source kind; constrain allowed actions to
  review-only actions; require explicit forbidden authority kinds.

### Edge 2: Settlement Request Could Become Settlement

- Risk:
  a request for later settlement review could be read as settling a relation or
  ratifying a claim.
- Response:
  keep settlement request posture separate from settlement outcome; reject
  rows that perform settlement, ratification, or truth declaration.

### Edge 3: Settlement Horizon Could Exceed Authority Profile

- Risk:
  a request could cite an authority profile that is not allowed to review the
  requested horizon.
- Response:
  require every request's settlement horizon to appear in every referenced
  authority profile's allowed relation horizons.

### Edge 4: Adversarial Review Could Become Unchecked Confidence

- Risk:
  no-counterevidence posture could be asserted without checked horizon or
  negative controls.
- Response:
  require checked horizon or negative-control refs; preserve inconclusive and
  blocked-by-source postures.

### Edge 5: Dissent Could Be Bypassed

- Risk:
  blocking dissent from `V76-A` could be ignored by settlement request rows.
- Response:
  settlement request validators must carry dissent refs or block readiness
  until dissent is reviewed.

### Edge 6: Majority Agreement Could Become Correctness

- Risk:
  agreement across projected/model outputs could be treated as correctness.
- Response:
  reject majority-as-correctness unless bounded relation review and authority
  coverage remain non-truth and non-settling.

### Edge 7: Gap Scan Could Become Implementation Priority

- Risk:
  gap rows could be treated as a work queue or implementation authorization.
- Response:
  gap scan rows remain review metadata only and carry required next surfaces
  without selecting downstream work.

### Edge 8: Downstream Authority Gaps Could Be Laundered

- Risk:
  product, runtime, release, external branch, dispatch-execution, or
  recursive-policy gaps could be converted into settlement readiness.
- Response:
  preserve those gaps as blockers or future-family pressure. `V76-B` cannot
  grant downstream authority.

### Edge 9: V76-B Could Begin V76-C

- Risk:
  the starter could accidentally add summary, handoff, or family closeout
  surfaces.
- Response:
  ship only authority profile, settlement request, adversarial relation
  review, and gap scan surfaces in `V76-B`; defer summaries and handoffs.

## Current Judgment

- `V76-B` is worth drafting now because `V76-A` has closed the source-bound
  claim / relation / dissent map on `main`.
- The second slice should stay review-only: it can make arbiter authority,
  settlement requests, adversarial relation review, and gap posture
  machine-checkable. It should not settle, ratify, execute, productize,
  release, activate external branches, or dispatch.
