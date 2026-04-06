# Assessment vNext+139 Edges

Status: pre-lock edge assessment for `V46-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS139_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Cross-Subject Comparison Reopens Baseline Or Perturbation Scorer Law

- Risk:
  the first comparison lane could quietly redefine released `V46-B` or `V46-C`
  semantics instead of consuming them.
- Response:
  bind subject records and comparison cases directly to released baseline and
  perturbation artifacts and forbid a second scorer family in `V46-D`.

### Edge 2: Comparison Collapses Into Ranking Doctrine

- Risk:
  the first cross-subject report could smuggle in leaderboard or promotion semantics
  instead of bounded diagnostic comparison.
- Response:
  keep the starter comparison report descriptive only and forbid ranking, winner
  selection, or promotional subject claims.

### Edge 3: Subject Pairs Drift Across Incompatible Contexts

- Risk:
  the first comparison lane could compare subjects across mismatched projection specs,
  execution contexts, baseline instances, or perturbation bundles.
- Response:
  require same released family spec, projection spec, baseline instance, and
  perturbation bundle across the starter pair, while replacing literal
  execution-context identity with a frozen compatibility law over:
  - `repo_snapshot_ref`
  - `tool_availability`
  - `context_budget_posture`
  - `determinism_posture`

### Edge 4: Comparison Evidence Stays Too Array-Like

- Risk:
  the comparison seam could remain deterministic while still hiding per-subject
  evidence behind parallel arrays.
- Response:
  require explicit subject summaries, field-level comparisons, and per-surface
  validation rows in the starter contracts.

### Edge 5: Subject Taxonomy Widens Too Fast

- Risk:
  the starter comparison lane could widen immediately into the full subject taxonomy
  from `V46-A` before the comparison law is stable.
- Response:
  freeze the starter subject-class subset to `base_model` and `prompted_model` only.

### Edge 5A: Comparison Semantics Stay Too Helper-Defined

- Risk:
  the starter comparison surfaces could look typed while still leaving
  `exact_match`, `different_but_comparable`, and `insufficient_evidence` to helper
  taste.
- Response:
  freeze finite per-surface comparison law over the released baseline metrics,
  perturbation non-regression, and perturbation validation fields only.

### Edge 6: Projection-Library Widening Reappears Inside The Comparison Starter

- Risk:
  `V46-D` could claim to be comparison-first while still widening into multiple new
  benchmark projections at the same time.
- Response:
  keep the starter slice bound to the released Procedural Depth projection only and
  defer broader projection-library work until later inside `V46-D` if needed.

## Current Judgment

- `V46-D` is the right next slice because the family now has:
  - released benchmark substrate (`V46-A`)
  - released baseline Procedural Depth projection (`V46-B`)
  - released perturbation and non-regression widening (`V46-C`)
- the safest next move is a comparison-first seam over that released stack:
  - not a reopening of scoring doctrine
  - not a projection-library explosion
  - not a downstream consumer seam
