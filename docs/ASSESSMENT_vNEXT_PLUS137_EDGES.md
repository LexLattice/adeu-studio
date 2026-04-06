# Assessment vNext+137 Edges

Status: post-closeout edge assessment for `V46-B` (April 6, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS137_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Concrete Projection Reopens Substrate Doctrine

- Risk:
  the first concrete procedural-depth slice could quietly redefine the released
  `V46-A` benchmark substrate instead of consuming it.
- Response:
  bind `V46-B` exactly to the released family spec, projection spec, and execution
  context, and forbid a second benchmark-substrate fork in this slice.
- Closeout Evidence:
  the shipped procedural-depth stack consumes the released `V46-A` artifact refs
  directly and introduces no second family/projection/execution-context schema family.

### Edge 2: Declared Contract Ids Drift From Released Artifacts

- Risk:
  the released `V46-A` projection spec already declared downstream procedural-depth
  contract ids, and `V46-B` could have shipped mismatched live ids.
- Response:
  require exact id parity between the `declared_*_contract_id` fields in the released
  projection spec and the actual released procedural-depth schema ids.
- Closeout Evidence:
  the shipped `adeu_procedural_depth_instance@1`,
  `adeu_procedural_depth_gold_trace@1`,
  `adeu_procedural_depth_run_trace@1`,
  `adeu_procedural_depth_metrics@1`, and
  `adeu_procedural_depth_diagnostic_report@1` surfaces match the declaration-only ids
  already carried by the released projection spec.

### Edge 3: Tiny Reference Chain Widens Into Benchmark-Library Sprawl

- Risk:
  the first concrete projection could widen from one tiny deterministic hierarchical
  chain into a broader library before perturbation or non-regression doctrine exists.
- Response:
  freeze `V46-B` to one tiny `hierarchical_3x3` reference chain only and defer wider
  perturbation/non-regression bundles to `V46-C`.
- Closeout Evidence:
  the released instance contract and committed fixtures admit one bounded
  `hierarchical_3x3` chain only, with no wider benchmark-library artifacts released.

### Edge 4: Imported Materialization Bug Reappears In Repo-Owned Instance Law

- Risk:
  the imported prototype computed procedural-depth instance ids before canonical step
  ordering was validated, which could make lawful payloads fail id checks.
- Response:
  require canonical structural validation before instance-id materialization and treat
  that imported bug as explicitly non-importable.
- Closeout Evidence:
  the shipped instance materialization path canonicalizes `step_specs` before id
  assignment, and review hardening extended the same canonicalization rule to the
  exported procedural-depth `compute_*_id` helpers.

### Edge 5: Gold Trace, Run Trace, And Evidence Refs Stay Too Thin

- Risk:
  the first scored benchmark projection could claim the released structural split
  while carrying event objects or support refs too thin to prove what failed.
- Response:
  require structurally rich event objects and trace-qualified support refs across the
  gold/run evidentiary layer.
- Closeout Evidence:
  shipped event objects carry `event_index`, `step_ref`, `step_role`, and bounded
  parent/return targeting, while `supporting_event_refs` remain trace-qualified across
  gold/run evidence.

### Edge 6: Metrics Collapse Into One-Number Benchmark Promotion

- Risk:
  the first metrics surface could over-collapse the structural split into a single
  promotion-ready benchmark number.
- Response:
  keep component fidelity surfaces explicit:
  - `plan_spine_fidelity`
  - `active_step_compilation_fidelity`
  - `reintegration_fidelity`
  - `dominant_failure_family`
  and forbid ranking/promotion semantics in the starter slice.
- Closeout Evidence:
  the shipped metrics contract keeps the three boolean component fidelities plus the
  bounded dominant-family field, and no ranking or one-number benchmark score shipped.

### Edge 7: Diagnostic Reports Overclaim Operational Authority

- Risk:
  the first diagnostic-report surface could be overread as routing, ranking, or
  training authority rather than bounded benchmark diagnosis.
- Response:
  keep `V46-B` diagnostic reports explicitly non-promotional and defer downstream
  consumer seams to `V46-E`.
- Closeout Evidence:
  the shipped diagnostic report remains bounded to trace-qualified supporting refs,
  interpretive summary, and limitations only, with no routing/ranking/training
  semantics released.

### Edge 8: Perturbation And Non-Regression Sneak Into The Baseline Projection

- Risk:
  the first concrete projection could silently grow repeated-run, perturbation, or
  non-regression semantics before those lanes are selected explicitly.
- Response:
  keep `V46-B` baseline-only and defer perturbation/non-regression to `V46-C`.
- Closeout Evidence:
  the shipped fixtures cover clean and degraded starter outcomes over one deterministic
  baseline chain only, and no perturbation/non-regression artifact family shipped in
  `v137`.

## Current Judgment

- `V46-B` was the right next slice because `V46-A` had already released the benchmark
  substrate and the family now needed one concrete Procedural Depth Fidelity stack.
- the shipped result remained properly bounded:
  - one repo-owned package
  - five released procedural-depth schemas
  - deterministic authoritative schema export plus root mirrors
  - deterministic `v46b` fixtures and scoring replay
  - explicit trace-qualified gold/run evidence refs
  - explicit boolean component fidelities
  - explicit `clean_success`, `horizontal_plan_spine`,
    `vertical_active_step_compilation`, `reintegration`, and `mixed` outcomes
  - canonical compute/materialize parity after review hardening
  - no perturbation/non-regression widening
  - no cross-subject comparison
  - no downstream consumer promotion seam
- `V46-B` is now closed on `main` in the branch-local sense:
  - procedural-depth instance
  - procedural-depth gold trace
  - procedural-depth run trace
  - procedural-depth metrics
  - procedural-depth diagnostic report
- the next meaningful slice is `V46-C`:
  - perturbation and non-regression widening over the released `V46-B` baseline
  - not a reopening of benchmark-substrate doctrine and not yet cross-subject or
    downstream consumer widening
