# Assessment vNext+139 Edges

Status: post-closeout edge assessment for `V46-D` (April 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS139_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Cross-Subject Comparison Reopens Released Scorer Law

- Risk:
  the first comparison lane could quietly redefine released `V46-B` or `V46-C`
  semantics instead of consuming them.
- Response:
  bind comparison artifacts directly to the released benchmark substrate, baseline, and
  perturbation stack and forbid a second scorer family in `V46-D`.
- Closeout Evidence:
  the shipped comparison lane reuses the released Procedural Depth run, metrics,
  diagnostic, non-regression, and benchmark-validation artifacts directly and ships no
  forked scorer family or schema-id branch.

### Edge 2: Comparison Collapses Into Ranking Doctrine

- Risk:
  the first cross-subject report could silently become leaderboard or promotion
  doctrine instead of bounded diagnostic comparison.
- Response:
  keep the starter comparison report descriptive only and forbid ranking, winner
  selection, routing authority, or training entitlement.
- Closeout Evidence:
  the shipped `V46-D` report remains bounded to descriptive
  `comparison_ready_clean` / `comparison_incompatible` posture only, with no ranking,
  routing, or training semantics.

### Edge 3: Subject Pairs Drift Across Incompatible Contexts

- Risk:
  the first comparison lane could compare subjects across mismatched execution
  contexts, mislabeled subject classes, or incompatible repo snapshots.
- Response:
  require exact compatibility over the frozen starter execution-context fields and keep
  subject-specific fields explicit rather than collapsed into one shared context id.
- Closeout Evidence:
  the shipped helper enforces one `base_model` plus one `prompted_model`,
  deterministic fixed context, exact compatibility over
  `repo_snapshot_ref` / `tool_availability` / `context_budget_posture` /
  `determinism_posture`, and review hardening now rejects subject-class drift against
  the bound execution context.

### Edge 4: Per-Subject Evidence Chain Can Become Mixed

- Risk:
  the comparison seam could accept a run trace, metrics payload, and diagnostic payload
  that validate individually but do not belong to the same released evidence chain.
- Response:
  require each subject summary to stay bound to one lawful baseline run/metric/diagnostic
  chain before cross-subject comparison begins.
- Closeout Evidence:
  review hardening now rejects baseline metric payloads that do not bind to the bound
  run trace and rejects diagnostic payloads that do not bind to the same run trace and
  metrics payload on both sides.

### Edge 5: Comparison Semantics Stay Too Helper-Defined

- Risk:
  `exact_match`, `different_but_comparable`, and `insufficient_evidence` could remain
  deterministic while still hiding the real comparison law inside helper taste.
- Response:
  freeze finite per-surface comparison law over:
  - `baseline_structural_fidelity`
  - `perturbation_non_regression`
  - `perturbation_validation`
- Closeout Evidence:
  the shipped comparison report materializes one explicit field-comparison row for each
  released starter surface and does not widen beyond those finite released comparisons.

### Edge 6: Projection-Library Widening Reappears Inside The Comparison Starter

- Risk:
  `V46-D` could widen into broader benchmark-library release while claiming to be only
  a comparison-first seam.
- Response:
  keep the starter slice bound to the released Procedural Depth projection only and
  defer broader projection-library work until later.
- Closeout Evidence:
  the shipped comparison lane consumes one released Procedural Depth baseline and one
  shared released perturbation bundle only, with no second benchmark projection family
  introduced.

## Current Judgment

- `V46-D` was the right next slice because the family already had:
  - released benchmark substrate (`V46-A`)
  - released baseline Procedural Depth projection (`V46-B`)
  - released perturbation and non-regression widening (`V46-C`)
- the shipped result remained properly bounded:
  - one repo-owned package
  - four released comparison schemas
  - one deterministic `base_model` versus `prompted_model` subject pair
  - exact execution-context compatibility law only
  - same released baseline instance and perturbation bundle only
  - descriptive comparison posture only
  - explicit per-subject summaries and per-surface comparisons only
  - fail-closed subject/context and baseline artifact-chain validation
  - no ranking
  - no projection-library widening
  - no downstream consumer seam
- `V46-D` is now closed on `main` in the branch-local sense:
  - benchmark subject record
  - cross-subject comparison case
  - cross-subject comparison report
  - cross-subject comparison validation report
- the next meaningful slice is `V46-E`:
  - a bounded downstream consumer seam over the now-released `V46-A` through `V46-D`
    benchmarking stack
  - not a reopening of benchmark-substrate doctrine and not yet a broad operational
    promotion or training-authority surface
