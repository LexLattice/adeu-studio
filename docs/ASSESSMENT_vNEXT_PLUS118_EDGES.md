# Assessment vNext+118 Edges

Status: planning-edge assessment for `V49-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS118_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V49-A` Contract Bypass

- Risk:
  the recovery lane could skip the released `V49-A` contracts and recover directly
  into ad hoc local structures.
- Response:
  require exactly one released parse profile in and exactly one released parse-result
  contract out.

### Edge 2: Heuristic Widening

- Risk:
  the first recovery slice could mint new relation kinds, lane tags, object kinds, or
  domains under the cover of natural-language parsing.
- Response:
  keep recovery bounded to released `V49-A` vocabularies and the starter domain
  `repo_policy_work` only.

### Edge 3: Candidate Distinctness Drift

- Risk:
  two implementations could emit different dedupe behavior while both claiming to
  produce the same typed result.
- Response:
  freeze candidate sameness to released `normal_form.semantic_hash` only and require
  dedupe before outcome classification.

### Edge 4: Candidate Ordering Drift

- Risk:
  alternative ordering could depend on incidental iteration order, alias scan order,
  or cartesian-product order.
- Response:
  require deterministic alternative ordering by canonical semantic hash before
  `candidate_rank` assignment.

### Edge 5: Outcome Boundary Drift

- Risk:
  behavior could blur the distinction between `typed_alternatives`,
  `clarification_required`, and `rejected_unsupported`.
- Response:
  freeze the outcome vocabulary and require committed fixtures for each starter
  outcome, including zero-candidate clarification posture.

### Edge 6: Unsupported Laundering

- Risk:
  unsupported inputs could be quietly coerced into apparent success.
- Response:
  require explicit `rejected_unsupported` posture driven by released unsupported
  patterns and out-of-domain detection.

### Edge 7: Alias / Anchor Precedence Drift

- Risk:
  the parser could silently invent precedence between exact anchors, aliases, partial
  matches, and conflicting cues.
- Response:
  freeze explicit precedence and require equal-strength conflicts to fail closed
  rather than choose silently.

### Edge 8: Clarification Shell Leakage

- Risk:
  the first recovery release could emit partial unresolved candidate shells and still
  call the result `clarification_required`.
- Response:
  freeze clarification to zero candidates only plus typed ambiguity diagnostics.

### Edge 9: Projection Leakage Into Identity

- Risk:
  explanatory evidence, notices, or ambiguity notes could quietly become effective
  identity fields.
- Response:
  explicitly reuse the released `V49-A` identity-versus-projection split inside all
  emitted recovery artifacts.

### Edge 10: Multi-Profile Or Multi-Domain Creep

- Risk:
  the first recovery release could overreach into profile selection, domain selection,
  or batched recovery.
- Response:
  freeze one input text, one released parse profile, and one starter domain only.

### Edge 11: Lowering Laundering

- Risk:
  the first recovery slice could quietly start performing deterministic lowering or
  `V48` seed emission.
- Response:
  defer all lowering to `V49-C` and all downstream bridge helpers to `V49-D`.

### Edge 12: Consumer Prematurity

- Risk:
  symbol audit, paper semantics, simulation, or product consumers could leak into the
  first recovery release and blur slice ownership.
- Response:
  keep `V49-B` bounded to parser behavior, fixtures, and targeted tests only.

## Current Judgment

- `V49-B` is worth implementing now because `V49-A` has already frozen the starter
  contracts, identity law, ambiguity posture, and unsupported posture on `main`.
- the next move should remain narrowly recovery-first: one bounded parser over one
  released profile and one starter domain before any lowering or downstream bridge is
  accepted.
