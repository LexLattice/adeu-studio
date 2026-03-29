# Assessment vNext+97 Edges

Status: planning-edge assessment for `V42-G3` (pre-lock).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS97_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Selection Register Drift

- Risk:
  harness execution could use puzzles outside the frozen selection register.
- Response:
  keep selection register authority typed and fail closed on undeclared puzzle IDs.

### Edge 2: Retrospective Swap and Order Drift

- Risk:
  outcomes could influence puzzle replacement or ordering after execution.
- Response:
  require exact canonical order from selection register and reject retrospective swap.

### Edge 3: Per-Puzzle Occupation Regression

- Risk:
  three-puzzle harness aggregation could keep refs while dropping `V42-G2` staged
  occupation rigor per puzzle.
- Response:
  require each puzzle entry to bind to a valid reasoning-run record with preserved
  stage-evidence posture.

### Edge 4: Cross-Puzzle Identity-Chain Breakage

- Risk:
  harness records could mix puzzle/run/session identity from different chains.
- Response:
  enforce one coherent identity chain across bundle/register/puzzle/run refs.

### Edge 5: Harness Sequence Non-Determinism

- Risk:
  the same three puzzles could produce non-replayable harness ordering/evidence layout.
- Response:
  require monotonic harness sequence register and deterministic replay over fixed
  emitted artifacts/evidence.

### Edge 6: Aggregation Contradiction

- Risk:
  harness-level local-eval/scorecard/submission refs could disagree with puzzle-run
  entries while still being accepted.
- Response:
  keep per-puzzle downstream refs explicit and validate optional aggregate refs against
  per-puzzle entries; fail closed on contradiction.

### Edge 7: Incomplete-Entry Laundering

- Risk:
  harness records could claim completion while omitting one canonical puzzle entry.
- Response:
  require exactly three canonical puzzle-entry slots in all accepted harness records,
  including blocked/failed outcomes.

### Edge 8: Cross-Run Config Drift

- Risk:
  three puzzle runs could be executed under differing hidden configurations while being
  interpreted as one comparable harness outcome.
- Response:
  enforce cross-puzzle agent/config identity consistency unless explicit typed
  divergence posture is declared.

### Edge 9: Scope Creep Into G4

- Risk:
  this slice could silently widen from bounded harness orchestration into behavior
  synthesis semantics.
- Response:
  keep `V42-G3` focused on deterministic three-puzzle orchestration; defer synthesis
  to `V42-G4`.

### Edge 10: Narrative Overclaim

- Risk:
  run summaries could be interpreted as authoritative over typed harness fields.
- Response:
  keep summary non-authoritative and subordinate to typed surfaces.

## Current Judgment

- `V42-G3` is the correct next seam after `V42-G2` because the remaining practical gap
  is deterministic bounded multi-puzzle harness orchestration over released control
  plane artifacts.
- The slice should be accepted only if three-puzzle selection authority, per-puzzle
  stage occupation carry-through, cross-puzzle identity/config coherence, exact-entry
  occupancy, and aggregation fail-closed checks are all machine-validated.
