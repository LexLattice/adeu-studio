# Assessment vNext+138 Edges

Status: post-closeout edge assessment for `V46-C` (April 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS138_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Perturbation Widening Reopens Baseline Scoring Law

- Risk:
  the first perturbation lane could quietly rewrite the released `V46-B` baseline
  scorer instead of consuming it.
- Response:
  require direct reuse of the released `V46-B` run, metrics, and diagnostic contracts
  and forbid a second baseline scorer family in `V46-C`.
- Closeout Evidence:
  the shipped perturbation bundle materializes repeated run traces against the released
  `V46-B` baseline stack directly and introduces no second scorer family or schema-id
  fork.

### Edge 2: Repeated-Run Stability Overclaims Empirical Reliability

- Risk:
  a tiny starter perturbation bundle could over-sound like broad empirical reliability
  doctrine rather than one bounded deterministic replay lane.
- Response:
  freeze starter replay count, freeze starter non-regression thresholds, and keep the
  slice diagnostic-only and bundle-scoped.
- Closeout Evidence:
  the shipped `V46-C` non-regression law stays fixed at replay count `3`, exact-match
  replay subjects only, and `deterministic_fixed_context` only, with no stochastic
  tolerance or variance-floor doctrine released.

### Edge 2A: Perturbation Cases Stay Too Label-Like

- Risk:
  the perturbation layer could ship named expectations without carrying enough
  operational information to materialize transformed starter runs.
- Response:
  require operational perturbation overlays over the released baseline run shape
  rather than label-only case shells.
- Closeout Evidence:
  the shipped perturbation-case contract carries ordered
  `perturbation_overlay_events`, optional bounded `output_summary_override`, and
  deterministic materialization into repeated run traces over the released baseline
  instance.

### Edge 3: Paraphrase-Preserving Cases Drift Into Answer-Only Equivalence

- Risk:
  a paraphrase-preserving perturbation could be over-scored by answer stability alone
  while ignoring structural procedure preservation.
- Response:
  keep released `V46-B` structural metrics authoritative and forbid answer-only
  equivalence as a substitute for procedural preservation.
- Closeout Evidence:
  the shipped perturbation lane still reuses released plan-spine, active-step, and
  reintegration scoring and does not introduce answer-only success law.

### Edge 4: Failure Topology Becomes Cross-Subject Comparison By Accident

- Risk:
  the first failure-topology artifact could quietly act like a comparison or ranking
  surface across systems rather than a bounded perturbation-bundle summary.
- Response:
  keep failure topology bundle-scoped only and defer cross-subject comparison to
  `V46-D`.
- Closeout Evidence:
  the released failure-topology artifact aggregates one bounded perturbation bundle
  over one released baseline only, with no cross-subject comparison, ranking, or
  projection-library widening.

### Edge 5: Non-Regression Reports Smuggle In Consumer Authority

- Risk:
  the first non-regression report could be overread as routing, model-promotion, or
  training authority instead of bounded benchmark diagnostics.
- Response:
  keep `V46-C` explicitly non-promotional and defer downstream consumer seams to
  `V46-E`.
- Closeout Evidence:
  the shipped non-regression and benchmark-validation artifacts remain diagnostic-only
  and bundle-scoped, with no routing, role-fit, or training-consumer semantics.

### Edge 6: Perturbation Bundle Widens Too Fast

- Risk:
  the family could jump from one released baseline chain to a broad perturbation
  library before the starter perturbation law is stable.
- Response:
  freeze `V46-C` to one small deterministic perturbation bundle only and defer wider
  projection-library work to `V46-D`.
- Closeout Evidence:
  the shipped `v46c` fixtures stay bounded to `branch_shift`, `delayed_constraint`,
  and `paraphrase_preserving` over the released `hierarchical_3x3` baseline only.

### Edge 6A: Aggregation Artifacts Stay Semantically Ambiguous

- Risk:
  failure topology, non-regression, and validation artifacts could remain
  deterministic while still hiding replay semantics inside parallel arrays.
- Response:
  require explicit per-case and per-replay structure across the starter aggregation
  artifacts.
- Closeout Evidence:
  the shipped failure-topology, non-regression, and benchmark-validation contracts
  carry per-case bundles with explicit replay-indexed refs rather than ambiguous
  parallel arrays.

### Edge 7: Deterministically Wrong Expectations Still Surface As Validation Success

- Risk:
  the perturbation bundle could remain replay-stable while still passing top-level
  validation even when expected dominant-family or terminal-status predictions are
  wrong.
- Response:
  require top-level validation aggregation to couple deterministic replay stability
  with expected-versus-observed agreement.
- Closeout Evidence:
  review hardening now requires `deterministic_replay_confirmed` to depend on both
  replay identity stability and expected/observed family and terminal-status
  agreement.

## Current Judgment

- `V46-C` was the right next slice because the family already had:
  - released benchmark substrate (`V46-A`)
  - released baseline Procedural Depth projection (`V46-B`)
- the shipped result remained properly bounded:
  - one repo-owned package
  - four released perturbation/non-regression schemas
  - one tiny deterministic perturbation bundle over the released baseline only
  - exact three-replay deterministic non-regression law only
  - explicit per-case and per-replay aggregation only
  - exact reuse of released `V46-B` dominant-family and terminal-status vocabularies
  - fail-closed unknown override handling and stricter top-level validation
  - no projection-library widening
  - no cross-subject comparison
  - no downstream consumer seam
- `V46-C` is now closed on `main` in the branch-local sense:
  - procedural-depth perturbation case
  - failure topology
  - non-regression report
  - procedural-depth benchmark validation report
- the next meaningful slice is `V46-D`:
  - cross-subject and comparison-first widening over the released `V46-B` and
    `V46-C` procedural-depth stack
  - not a reopening of benchmark-substrate doctrine and not yet the downstream
    consumer seam
