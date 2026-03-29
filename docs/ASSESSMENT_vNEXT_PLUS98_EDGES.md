# Assessment vNext+98 Edges

Status: planning-edge assessment for `V42-G4` (pre-lock).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS98_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Harness-Binding Drift

- Risk:
  behavior synthesis could drift away from one released three-puzzle harness input.
- Response:
  enforce typed binding to one released `adeu_arc_three_puzzle_harness_record@1` and
  reject mixed or ambient selection posture.

### Edge 2: Per-Puzzle Ordering Drift

- Risk:
  behavior entries could reorder or omit puzzle identities while still appearing valid.
- Response:
  require canonical per-puzzle order equal to released harness selection order; fail
  closed on order/identity drift.

### Edge 3: Missing Evidence Anchors

- Risk:
  failure-mode claims could be emitted without typed upstream evidence anchors.
- Response:
  require typed evidence refs for behavior signals and failure-mode catalog entries.

### Edge 4: Claim-Posture Laundering

- Risk:
  narrative synthesis could convert bounded local evidence into unsupported readiness or
  necessity claims.
- Response:
  require typed claim-posture registers with explicit uncertainty/constraint posture and
  reject unsupported claim classes.

### Edge 5: Authority-Boundary Inversion

- Risk:
  run summaries could be treated as authoritative over typed upstream control-plane
  surfaces.
- Response:
  keep narrative non-authoritative and subordinate to typed behavior identity/evidence
  fields.

### Edge 6: Cross-Puzzle Pattern Overclaim

- Risk:
  cross-puzzle synthesis could infer durable strategy claims from weak or contradictory
  upstream evidence.
- Response:
  require cross-puzzle pattern entries to cite explicit support refs to per-puzzle
  behavior entries and typed evidence refs; require all-three support when claiming
  all-three shared tendency.

### Edge 7: Failure Taxonomy Drift

- Risk:
  failure modes could degrade into ad hoc labels that cannot be compared across bundles.
- Response:
  require stable typed taxonomy fields (`failure_mode_id`, `failure_mode_kind`,
  `failure_mode_scope`, `evidence_refs`, `claim_posture`) for each catalog entry.

### Edge 8: Deterministic Replay Overclaim

- Risk:
  `V42-G4` replay language could be interpreted as deterministic fresh model
  re-execution.
- Response:
  pin deterministic replay scope to fixed emitted upstream artifacts plus fixed evidence
  refs only.

### Edge 9: Solver-Authority Minting

- Risk:
  synthesis outputs could mint new semantic solver/puzzle-rule/capability authority not
  present in upstream typed artifacts.
- Response:
  explicitly forbid authority minting in `V42-G4`; constrain synthesis to evidence
  mapping over released typed surfaces only.

### Edge 10: Premature Product/Execution Widening

- Risk:
  behavior-evidence synthesis could silently widen into benchmark-tournament execution
  or operator surface release.
- Response:
  keep `V42-G4` bounded to local synthesis outputs only; defer tournament/API/web and
  generalized orchestration seams.

## Current Judgment

- `V42-G4` is the correct next seam after released `V42-G3` because the remaining
  practical gap is canonical behavior-evidence synthesis with typed authority boundaries
  over already bounded harness outputs.
- The slice should be accepted only if synthesis remains strictly traceable to released
  typed artifacts, preserves fail-closed claim/evidence posture, and avoids runtime
  widening outside the bounded local ARC lane.
