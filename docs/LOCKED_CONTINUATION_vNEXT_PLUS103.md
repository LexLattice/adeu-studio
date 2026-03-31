# Locked Continuation vNext+103

Status: `V45-D` implementation contract.

## V103 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45d_repo_test_intent_matrix_contract@1",
  "target_arc": "vNext+103",
  "target_path": "V45-D",
  "target_scope": "repo_test_intent_matrix_over_released_v45a_v45b_v45c_descriptive_baseline",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_to_V42_released_stack_plus_V45-A_V45-B_V45-C_released_descriptive_surfaces_on_main",
  "governing_stack_consumption_mode": "descriptive_consumption_not_release_gating_or_mutation_authority_minting",
  "repo_test_intent_matrix_schema": "repo_test_intent_matrix@1",
  "repo_symbol_catalog_schema": "repo_symbol_catalog@1",
  "repo_dependency_graph_schema": "repo_dependency_graph@1",
  "descriptive_plane_first_required": true,
  "bounded_python_test_surface_required": true,
  "repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "test_source_set_binding_required": true,
  "test_source_set_hash_required": true,
  "released_v45b_binding_required": true,
  "top_level_extraction_posture_required": true,
  "top_level_extraction_method_required": true,
  "typed_test_intent_entry_required": true,
  "test_claim_assertion_unit_row_granularity_required": true,
  "claimed_vs_observed_distinction_required": true,
  "claimed_invariant_binding_required": true,
  "observed_assertion_surface_required": true,
  "confidence_posture_required": true,
  "gating_posture_required": true,
  "invariant_domain_required": true,
  "guarded_surface_ref_kind_model_required": true,
  "source_artifact_refs_required": true,
  "cross_artifact_snapshot_source_consistency_required": true,
  "internal_guarded_surface_resolution_required": true,
  "bounded_vocabulary_note_required": true,
  "aspirational_invariant_claim_rejection_required": true,
  "authority_posture_non_promotional_required": true,
  "automatic_release_gating_promotion_forbidden": true,
  "optimization_register_release_deferred": true,
  "descriptive_to_normative_binding_deferred": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "source_architecture_doc": "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
  "decomposition_doc": "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
}
```

## Slice

- Arc label: `vNext+103`
- Family label: `V45-D`
- Scope label: bounded repo test-intent matrix over one repo snapshot

## Objective

Release the bounded `V45-D` test-intent lane by materializing:

- one canonical `repo_test_intent_matrix@1`;

while preserving snapshot identity, explicit bounded test-source binding, explicit
claimed-vs-observed separation, bounded confidence and gating posture, explicit binding
to the released `V45-B` symbol/dependency baseline, and fail-closed rejection of
aspirational invariant claims, untyped guarded-surface refs, or authority laundering.

This slice is descriptive test-intent compilation, not release-gating authority,
optimization entitlement, or descriptive-to-normative binding.

## Frozen Implementation Decisions

1. Descriptive-first strategy:
   - `V45-D` emits typed test-intent visibility only;
   - outputs may constrain later planning but may not mint release-gating,
     optimization, scheduling, or mutation authority.
2. Path-order strategy:
   - `V45-A`, `V45-B`, and `V45-C` remain authoritative released descriptive baselines
     on `main`;
   - this contract follows the current `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md` ladder and
     does not remap older pre-`v28` seed vocabulary;
   - `V45-D` is the next widening because later `V45-E` and `V45-F` need explicit
     test-to-invariant visibility in addition to released schema, symbol, dependency,
     and planning-surface registers.
3. Source authority strategy:
   - all emitted artifacts must bind to one explicit repo-visible snapshot identity and
     one explicit bounded Python test source set;
   - the artifact must also bind one explicit test-source-set hash and one explicit
     extraction posture/method pair;
   - stale-snapshot semantics must be explicit rather than implied;
   - outputs are valid for the bound snapshot only and become historical evidence when
     stale.
4. Cross-artifact binding strategy:
   - `repo_test_intent_matrix@1` must bind to one released or same-run
     `repo_symbol_catalog@1` and one released or same-run `repo_dependency_graph@1`
     over the same snapshot/source baseline;
   - internal guarded-surface refs must resolve against the bound `V45-B` code
     surfaces;
   - the bound dependency graph exists to explain helper, fixture, and
     module-boundary reachability between the test row and the guarded surface, not to
     prove invariant defense by itself;
   - out-of-scope guarded surfaces must use explicit boundary typing rather than
     dangling strings.
5. Test-row modeling strategy:
   - row granularity is frozen as one row per test-claim/assertion unit rather than one
     row per whole test file or whole test function;
   - each row must therefore carry stable identity, explicit `test_ref`, `test_kind`,
     one typed `guarded_surface_ref`, one typed `claimed_invariant_binding`, one typed
     `observed_assertion_surface`, `invariant_domain`, `gating_posture`,
     `confidence_posture`, explicit derivation posture/method, and explicit source
     artifact refs;
   - the first release stays bounded to Python test surfaces and Python guarded
     code-surface refs only.
6. Claimed-vs-observed strategy:
   - claimed invariant binding and observed assertion surface must remain distinct
     fields rather than being collapsed into one prose summary;
   - naming-only or docstring-only invariant claims are insufficient without observed
     assertion support or explicit adjudication.
7. Confidence strategy:
   - confidence posture expresses support strength for the claimed invariant link;
   - confidence posture may not be overread as truth, release authority, or settlement
     by itself.
8. Anti-overreach strategy:
   - `V45-D` may not present hotspot, concentration, or strong-dependency findings as
     optimization entitlement;
   - `V45-D` may not present inferred test importance as automatic release-gating
     authority;
   - `V45-D` may not widen into `V45-E` or `V45-F`.

## Bounded Vocabulary Note

The first `V45-D` release should freeze bounded starter vocabularies for the new typed
fields rather than leaving them to implementation taste.

The intended bounded starter vocabularies are:

- `test_kind`:
  - `pytest_function`
  - `pytest_method`
- `invariant_domain`:
  - `ontology`
  - `epistemics`
  - `deontics`
  - `utility`
  - `mixed`
- `gating_posture`:
  - `release_gating`
  - `advisory`
  - `informational`
- `derivation_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `derivation_method`:
  - `assertion_ast`
  - `fixture_or_helper_binding`
  - `test_name_convention`
  - `bounded_inference_rule`
  - `adjudicated_policy`
- `confidence_posture`:
  - `low`
  - `medium`
  - `high`
  - `adjudicated`
  - `settled`
- `guarded_surface_ref_kind`:
  - `internal_symbol`
  - `internal_module_boundary`
  - `external_boundary`
- `assertion_surface_kind`:
  - `assert_statement`
  - `pytest_raises`
  - `equality_assertion`
  - `predicate_call_assertion`
  - `response_or_status_assertion`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent vocabulary creep.

## Required Deliverables

1. New typed descriptive surface:
   - canonical `repo_test_intent_matrix@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic extraction entrypoint(s) that:
   - consume one explicit repo snapshot and one bounded Python test source set;
   - bind to one explicit `V45-B` symbol/dependency baseline over the same
     snapshot/source posture;
   - derive typed test-intent rows with explicit claimed invariant bindings, observed
     assertion surfaces, invariant domain, gating posture, confidence posture,
     derivation posture/method, and typed evidence refs;
   - fail closed on unsupported claims, drifted bindings, malformed source binding,
     untyped boundary refs, or authority laundering posture.
3. Top-level schema anchors for `repo_test_intent_matrix@1`:
   - `schema`
   - `repo_test_intent_matrix_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `test_source_set`
   - `test_source_set_hash`
   - `bound_symbol_catalog_ref`
   - `bound_dependency_graph_ref`
   - `matrix_scope`
   - `extraction_posture`
   - `extraction_method`
   - `test_intent_entries`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per test-intent entry anchors:
     - `entry_id`
     - `test_ref`
     - `test_kind`
     - `guarded_surface_ref`
     - per guarded-surface-ref anchors:
       - `guarded_surface_ref_kind`
       - `guarded_surface_ref_value`
     - `claimed_invariant_binding`
     - per claimed-invariant-binding anchors:
       - `binding_id`
       - `binding_statement`
     - `observed_assertion_surface`
     - per observed-assertion-surface anchors:
       - `assertion_surface_kind`
       - `assertion_source_ref`
       - `assertion_summary`
     - `invariant_domain`
     - `gating_posture`
     - `confidence_posture`
     - `derivation_posture`
     - `derivation_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
4. Deterministic laws that fail closed on at least:
   - missing snapshot identity/hash binding;
   - missing or empty bounded test source set binding;
   - missing test-source-set hash;
   - missing bound symbol/dependency baseline refs or mismatched snapshot/source
     identity between the matrix and the bound `V45-B` surfaces;
   - missing top-level extraction posture or extraction method;
   - any entry missing required test, claim, observed-assertion, gating, confidence, or
     derivation fields;
   - any entry missing source artifact refs;
   - any `source_artifact_ref` that does not resolve inside the declared
     `test_source_set`;
   - duplicate entry IDs;
   - any internal guarded-surface ref that does not resolve against the bound
     `repo_symbol_catalog@1` or declared internal module-boundary namespace under the
     same snapshot/source baseline;
   - any guarded-surface ref carrying out-of-scope targets without valid boundary
     typing;
   - any row claiming invariant defense without observed assertion support;
   - any row whose confidence or gating posture overclaims beyond the observed
     assertion surface;
   - any row carrying optimization, scheduling, mutation, or release entitlement as an
     authoritative outcome.
5. Committed reference fixtures under `apps/api/fixtures/repo_description/vnext_plus103/`:
   - one accepted test-intent-matrix reference fixture;
   - one rejected fixture with missing snapshot identity;
   - one rejected fixture with mismatched `V45-B` snapshot/source binding;
   - one rejected fixture with claimed invariant binding but no observed assertion
     surface;
   - one rejected fixture with guarded-surface ref lacking valid boundary typing;
   - one rejected fixture with release-gating or optimization entitlement laundering.
6. Python tests covering:
   - schema/model validation for test-intent-matrix artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for accepted fixtures;
   - rejection of identity/source/claim/authority contradictions;
   - cross-artifact consistency between the matrix and the bound `V45-B` symbol and
     dependency surfaces.

## Hard Constraints

- `vNext+103` may not reopen or redefine released `V41`, `V42`, `V45-A`, `V45-B`, or
  `V45-C` contracts.
- `vNext+103` may not widen into optimization-register release or recursive-governance
  binding.
- `vNext+103` must keep outputs descriptive-first and non-promotional.
- `vNext+103` may not treat inferred test importance as automatic release-gating
  authority.
- `vNext+103` may not treat hotspot, dependency, or concentration findings as
  optimization entitlement.
- `vNext+103` outputs must remain snapshot-bound and historical when stale.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- test-intent schema release, deterministic extraction, `V45-B` cross-artifact binding,
  fixture ladder, and fail-closed validation are one tightly coupled seam;
- splitting them would create temporary contract drift for the same bounded `V45-D`
  lane.
