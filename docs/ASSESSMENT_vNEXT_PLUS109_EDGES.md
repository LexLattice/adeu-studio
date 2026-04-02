# Assessment vNext+109 Edges

Status: post-closeout edge assessment for `V47-D` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS109_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Owner-Layer Vocabulary Drift

- Risk:
  `V47-D` could have introduced a new bootstrap owner-layer term that drifts from the
  earlier released bootstrap vocabulary instead of projecting it consistently.
- Response:
  freeze one normalized bootstrap owner-layer term for ownership-profile rows and make
  explicit that it is the same bootstrap concept already used by released bootstrap
  predicate-contract surfaces.
- Closeout Evidence:
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  `packages/adeu_commitments_ir/tests/fixtures/v47d/reference_anm_selector_predicate_ownership_profile.json`,
  and test `test_v47d_vocabularies_are_exact`.

### Edge 2: Implicit Selector Promotion

- Risk:
  bootstrap string selectors could be silently reinterpreted as imported O-owned
  selector handles by naming or code convention alone.
- Response:
  require explicit selector ref kind, explicit selector owner layer, and explicit
  imported handle refs where owned posture is claimed.
- Closeout Evidence:
  selector-row validation in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  accepted transition spec
  `packages/adeu_semantic_source/tests/fixtures/v47d/reference_ownership_spec.json`,
  reject spec
  `packages/adeu_semantic_source/tests/fixtures/v47d/reject_implicit_selector_promotion_spec.json`,
  and tests `test_v47d_reference_profile_replays_deterministically` and
  `test_v47d_rejects_implicit_selector_promotion`.

### Edge 3: Implicit Predicate Promotion

- Risk:
  bootstrap predicate contracts could be silently reinterpreted as imported E-owned
  predicate-registry bindings without typed transition doctrine.
- Response:
  require explicit predicate ref kind, explicit predicate owner layer, and explicit
  imported registry refs where owned posture is claimed.
- Closeout Evidence:
  predicate-row validation in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  accepted transition spec
  `packages/adeu_semantic_source/tests/fixtures/v47d/reference_ownership_spec.json`,
  committed ownership profile fixture, and deterministic replay in
  `test_v47d_reference_profile_replays_deterministically`.

### Edge 4: Row Mutual-Exclusion Drift

- Risk:
  selector or predicate rows could carry both bootstrap and imported ref fields at
  once, leaving contradictory mixed state inside a single row.
- Response:
  freeze explicit per-row mutual-exclusion invariants tying ref kind, owner layer, and
  required/forbidden ref fields together.
- Closeout Evidence:
  `SelectorOwnershipRow` / `PredicateOwnershipRow` validation in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  compile-time row enforcement in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  and tests `test_v47d_rejects_selector_row_with_conflicting_bootstrap_and_imported_fields`
  and `test_v47d_rejects_implicit_selector_promotion`.

### Edge 5: Compatibility-Matrix Thinness

- Risk:
  compatibility posture could stay persuasive in prose while the actual bootstrap vs
  owned combinations remain under-specified.
- Response:
  require a first-class compatibility matrix covering the four selector/predicate
  ownership combinations with explicit allowed/forbidden, replay, later-lock, and
  mixed-ownership-constrained fields.
- Closeout Evidence:
  committed profile fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47d/reference_anm_selector_predicate_ownership_profile.json`,
  validation in `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and tests `test_v47d_rejects_incomplete_compatibility_matrix` and
  `test_v47d_rejects_missing_present_compatibility_combination`.

### Edge 6: Bootstrap Retirement Laundering

- Risk:
  a slice could imply that bootstrap selectors/predicate contracts are retired without
  the later-lock posture needed to authorize that retirement.
- Response:
  require explicit bootstrap-retirement posture and fail closed when retirement is
  claimed without later-lock binding.
- Closeout Evidence:
  `bootstrap_retirement_posture` typing and invariants in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  explicit retirement rows in the committed `v47d` profile fixture,
  and bounded retirement posture in
  `packages/adeu_semantic_source/tests/fixtures/v47d/reference_ownership_spec.json`.

### Edge 7: Imported-Ref Resolution Drift

- Risk:
  imported selector handles or predicate-registry refs could be dangling, stale, or
  identity/version incompatible while still looking syntactically valid.
- Response:
  require imported refs to resolve fail closed against the declared snapshot,
  source-scope, and declared identity/version binding.
- Closeout Evidence:
  imported-registry resolution in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  reject specs `reject_dangling_imported_selector_spec.json` and
  `reject_incompatible_imported_predicate_version_spec.json`,
  plus tests `test_v47d_rejects_dangling_imported_selector_handle` and
  `test_v47d_rejects_incompatible_imported_predicate_version`.

### Edge 8: Snapshot / Source-Scope Drift

- Risk:
  ownership-transition rows could bind together incompatible snapshots or source scopes
  and still look structurally plausible.
- Response:
  require same snapshot identity and explicit artifact-local source-scope compatibility
  checks.
- Closeout Evidence:
  same-snapshot/source-scope checks in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  accepted transition spec
  `packages/adeu_semantic_source/tests/fixtures/v47d/reference_ownership_spec.json`,
  and deterministic replay coverage in
  `test_v47d_reference_profile_replays_deterministically`.

### Edge 9: Backward-Compatibility Erasure

- Risk:
  the ownership-transition lane could break replay or interpretation of released
  bootstrap `V47-A` / `V47-B` / `V47-C` artifacts while claiming compatibility.
- Response:
  require explicit backward-compatible bootstrap replay and reject silent semantic
  reinterpretation.
- Closeout Evidence:
  accepted bootstrap-only spec
  `packages/adeu_semantic_source/tests/fixtures/v47d/bootstrap_only_ownership_spec.json`,
  bootstrap-only replay test
  `test_v47d_bootstrap_only_profile_preserves_released_replay`,
  and committed `bootstrap_only` compatibility rows in the `v47d` profile fixture.

### Edge 10: Authority Leakage Through Owned Surfaces

- Risk:
  imported owned selector/predicate posture could be overread as authority to mint
  execution, approval, migration, or consumer-binding powers.
- Response:
  keep the slice explicitly non-executive, non-migratory, and non-consumer-binding,
  with anti-leakage reject fixtures and compatibility-matrix constraints.
- Closeout Evidence:
  frozen `V47-D` lock scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md`,
  bounded implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py` and
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and mixed-ownership validation tests
  `test_v47d_rejects_present_mixed_combination_marked_forbidden` and
  `test_v47d_rejects_allowed_row_with_forbidden_posture`.

### Edge 11: Schema/Fixture Drift

- Risk:
  typed ownership doctrine could look clean in prose while authoritative schema,
  mirrored schema, and accepted fixtures drift apart.
- Response:
  require parity across docs, authoritative schema, mirrored schema, and committed
  fixtures for the released ownership profile.
- Closeout Evidence:
  `packages/adeu_commitments_ir/schema/anm_selector_predicate_ownership_profile.v1.json`,
  `spec/anm_selector_predicate_ownership_profile.schema.json`,
  committed profile fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47d/reference_anm_selector_predicate_ownership_profile.json`,
  and tests `packages/adeu_commitments_ir/tests/test_export_schema.py` and
  `packages/adeu_commitments_ir/tests/test_anm_selector_predicate_ownership_profile.py`.

### Edge 12: Package-Boundary Sprawl

- Risk:
  an ownership-transition lane could sprawl into unrelated packages or downstream
  consumers before the bounded profile surface is stable.
- Response:
  keep `V47-D` bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.
- Closeout Evidence:
  shipped implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and bounded package selection in `docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md`.

## Current Judgment

- `V47-D` was the right next move because `V47-A` through `V47-C` had already released
  the bounded ANM substrate, hardening layer, and coexistence/adoption doctrine on
  `main`, while explicit ownership transition remained the next unclosed gap.
- `V47-D` on `main` now resolves that gap by shipping one typed ownership-transition
  profile with normalized bootstrap owner-layer continuity, explicit bootstrap-vs-owned
  selector/predicate rows, a four-combination compatibility matrix, and fail-closed
  imported-ref resolution.
- the shipped seam remains doctrine-first and non-authorizing, so later `V47-E+`
  downstream-consumer lanes can build on it without being silently authorized by
  owned-surface existence alone.
