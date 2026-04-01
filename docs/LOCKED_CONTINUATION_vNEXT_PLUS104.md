# Locked Continuation vNext+104

Status: `V45-E` implementation contract.

## V104 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45e_repo_optimization_register_contract@1",
  "target_arc": "vNext+104",
  "target_path": "V45-E",
  "target_scope": "repo_optimization_register_over_released_v45a_v45b_v45c_v45d_descriptive_baseline",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_to_V42_released_stack_plus_V45-A_V45-B_V45-C_V45-D_released_descriptive_surfaces_on_main",
  "governing_stack_consumption_mode": "descriptive_consumption_not_mutation_or_normative_authority_minting",
  "repo_optimization_register_schema": "repo_optimization_register@1",
  "repo_entity_catalog_schema": "repo_entity_catalog@1",
  "repo_schema_family_registry_schema": "repo_schema_family_registry@1",
  "repo_symbol_catalog_schema": "repo_symbol_catalog@1",
  "repo_dependency_graph_schema": "repo_dependency_graph@1",
  "repo_test_intent_matrix_schema": "repo_test_intent_matrix@1",
  "descriptive_plane_first_required": true,
  "bounded_repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "source_set_binding_required": true,
  "source_set_hash_required": true,
  "released_v45a_v45b_v45c_v45d_binding_required": true,
  "top_level_extraction_posture_required": true,
  "top_level_extraction_method_required": true,
  "typed_optimization_entry_required": true,
  "descriptive_finding_vs_optimization_candidate_vs_amendment_entitlement_distinction_required": true,
  "compression_axis_required": true,
  "optimization_posture_required": true,
  "support_basis_required": true,
  "secondary_compression_axes_support_required": true,
  "secondary_support_basis_tags_support_required": true,
  "priority_posture_required": true,
  "source_artifact_refs_required": true,
  "cross_artifact_snapshot_identity_and_source_scope_compatibility_required": true,
  "cross_surface_cluster_carrier_required": true,
  "bounded_vocabulary_note_required": true,
  "diagnostic_to_amendment_boundary_required": true,
  "automatic_mutation_permission_forbidden": true,
  "automatic_priority_or_scheduling_authority_forbidden": true,
  "recursive_governance_binding_deferred": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "source_architecture_doc": "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
  "decomposition_doc": "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
}
```

## Slice

- Arc label: `vNext+104`
- Family label: `V45-E`
- Scope label: bounded repo optimization register over one repo snapshot

## Objective

Release the bounded `V45-E` optimization-register lane by materializing:

- one canonical `repo_optimization_register@1`;

while preserving snapshot identity, explicit bounded source-set posture, explicit
descriptive finding versus optimization candidate separation, explicit non-equivalence
between surfaced diagnostics and amendment entitlement, explicit binding back to the
released `V45-A` through `V45-D` descriptive baselines, and fail-closed rejection of
priority laundering, mutation laundering, or unsupported optimization claims.

This slice is descriptive optimization diagnostics, not mutation permission,
refactor/scheduling authority, or recursive-governance binding.

## Frozen Implementation Decisions

1. Descriptive-first strategy:
   - `V45-E` emits typed optimization diagnostics only;
   - outputs may constrain later planning but may not mint mutation, scheduling,
     release-gating, or settlement authority.
2. Path-order strategy:
   - `V45-A`, `V45-B`, `V45-C`, and `V45-D` remain authoritative released descriptive
     baselines on `main`;
   - this contract follows the current `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md` ladder and
     does not reopen older pre-`v28` path assignments;
   - `V45-E` is the next widening because later `V45-F` work needs an explicit
     diagnostic object for hotspot, consolidation, and compression candidates instead
     of diffuse prose review notes.
3. Source authority strategy:
   - all emitted artifacts must bind to one explicit repo-visible snapshot identity and
     one explicit bounded source set over the consumed descriptive inputs;
   - the artifact must also bind one explicit source-set hash and one explicit
     extraction posture/method pair;
   - stale-snapshot semantics must be explicit rather than implied;
   - outputs are valid for the bound snapshot only and become historical evidence when
     stale.
4. Cross-artifact binding strategy:
   - `repo_optimization_register@1` must bind to one released or same-run
     `repo_entity_catalog@1`, `repo_schema_family_registry@1`, `repo_symbol_catalog@1`,
     `repo_dependency_graph@1`, and `repo_test_intent_matrix@1` over the same
     snapshot identity with explicit artifact-local source-scope compatibility rather
     than a falsely unified source-set model;
   - optimization entries may cite released dependency and test-intent surfaces as
     descriptive support but may not collapse them into mutation or gating authority;
   - any internal surface reference must resolve against one of the bound released
     descriptive artifacts under the same snapshot-compatible baseline;
   - `finding_scope_ref` may resolve either inside the declared `source_set` or inside
     one of the explicitly bound `V45-A` through `V45-D` artifacts under the same
     snapshot-compatible baseline.
5. Optimization-entry modeling strategy:
   - row granularity is frozen as one row per surfaced diagnostic unit rather than one
     row per whole file or whole package;
   - each row must therefore carry stable identity, one explicit `finding_scope`,
     `compression_axis`, `optimization_posture`, `support_basis`, optional
     `secondary_compression_axes`, optional `secondary_support_basis_tags`,
     `descriptive_finding_summary`, `optimization_candidate_summary`,
     `priority_posture`, `amendment_entitlement`, explicit derivation
     posture/method, and explicit source artifact refs;
   - the first release stays bounded to repo-internal descriptive surfaces only.
6. Diagnostic-to-amendment strategy:
   - descriptive findings, optimization candidates, and amendment entitlement must
     remain distinct fields rather than being collapsed into one summary;
   - the first release must freeze `amendment_entitlement` to a fail-closed negative
     posture only;
   - surfaced hotspot or consolidation signals are diagnostic objects, not execution
     instructions.
7. Support strategy:
   - every optimization row must expose the descriptive basis that supports it, such as
     concentration, duplication, invariant-restatement drift, or cross-surface burden;
   - naming-only or file-size-only claims are insufficient without explicit support
     basis and source-artifact grounding.
8. Anti-overreach strategy:
   - `V45-E` may not present hotspots as automatic split entitlement;
   - `V45-E` may not present duplication signals as abstraction entitlement;
   - `V45-E` may not present surfaced candidates as priority or scheduling authority;
   - `V45-E` may not widen into `V45-F`.

## Bounded Vocabulary Note

The first `V45-E` release should freeze bounded starter vocabularies for the new typed
fields rather than leaving them to implementation taste.

The intended bounded starter vocabularies are:

- `compression_axis`:
  - `structural_compression`
  - `semantic_compression`
  - `governance_compression`
  - `surface_compression`
- `optimization_posture`:
  - `hotspot`
  - `consolidation_candidate`
  - `justified_monolith`
  - `temporary_concentration`
  - `forbidden_drift_zone`
- `support_basis`:
  - `duplicate_abstraction_signal`
  - `repeated_law_expression`
  - `cross_surface_invariant_restated`
  - `long_file_or_concentrated_surface`
  - `test_and_dependency_concentration`
- `priority_posture`:
  - `informational_only`
  - `planning_candidate`
  - `adjudication_required`
- `amendment_entitlement`:
  - `not_authorized_by_this_artifact`
- `derivation_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `derivation_method`:
  - `descriptive_projection`
  - `bounded_signal_rule`
  - `cross_artifact_join`
  - `adjudicated_policy`
- `finding_scope_kind`:
  - `file_surface`
  - `module_surface`
  - `schema_surface`
  - `test_surface`
  - `cross_surface_cluster`

Secondary compression-axis and support-basis tags, when present, must reuse the same
bounded starter vocabularies as their primary fields rather than inventing parallel
taxonomies.

`cross_surface_cluster` member refs, when present, must use the same bounded
surface-kind vocabulary as ordinary finding scopes except that nested
`cross_surface_cluster` members are forbidden in this slice.

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent vocabulary creep.

## Required Deliverables

1. New typed descriptive surface:
   - canonical `repo_optimization_register@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic extraction entrypoint(s) that:
   - consume one explicit repo snapshot and one bounded source set over the released
     descriptive baselines;
   - bind to released `V45-A` through `V45-D` artifacts over the same
     snapshot identity and explicit artifact-local source-scope compatibility posture;
   - derive typed optimization rows with explicit compression axis, optimization
     posture, support basis, descriptive-finding summary, optimization-candidate
     summary, priority posture, fixed non-authorizing amendment-entitlement posture,
     explicit derivation posture/method, optional bounded secondary tags, and typed
     evidence refs;
   - fail closed on unsupported optimization claims, malformed source binding, missing
     cross-artifact binding, missing support basis, or authority laundering posture.
3. Top-level schema anchors for `repo_optimization_register@1`:
   - `schema`
   - `repo_optimization_register_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `source_set`
   - `source_set_hash`
   - `bound_entity_catalog_ref`
   - `bound_schema_family_registry_ref`
   - `bound_symbol_catalog_ref`
   - `bound_dependency_graph_ref`
   - `bound_test_intent_matrix_ref`
   - `register_scope`
   - `extraction_posture`
   - `extraction_method`
   - `optimization_entries`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per optimization entry anchors:
     - `entry_id`
     - `finding_scope`
     - per finding-scope anchors:
       - `finding_scope_kind`
       - `finding_scope_ref`
       - `cluster_member_refs` when `finding_scope_kind = cross_surface_cluster`
       - per cluster-member-ref anchors:
         - `member_ref_kind`
         - `member_ref`
     - `compression_axis`
     - `optimization_posture`
     - `support_basis`
     - `secondary_compression_axes`
     - `secondary_support_basis_tags`
     - `descriptive_finding_summary`
     - `optimization_candidate_summary`
     - `priority_posture`
     - `amendment_entitlement`
     - `derivation_posture`
     - `derivation_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
4. Deterministic laws that fail closed on at least:
   - missing snapshot identity/hash binding;
   - missing or empty bounded source set binding;
   - missing source-set hash;
   - missing any bound `V45-A` through `V45-D` reference or mismatched
     snapshot/source-scope compatibility posture between the register and those bound
     descriptive artifacts;
   - missing top-level extraction posture or extraction method;
   - any entry missing required scope, compression, posture, support, summary,
     priority, entitlement, derivation, or source-artifact fields;
   - any `source_artifact_ref` that does not resolve inside the declared `source_set`;
   - duplicate entry IDs;
   - any finding scope that does not resolve against the bound descriptive baseline or
     a valid cross-surface cluster representation under the same
     snapshot-compatible baseline;
   - any `cross_surface_cluster` row lacking explicit cluster-member refs or carrying
     cluster members that do not resolve against the declared `source_set` or one of
     the bound descriptive artifacts;
   - any entry whose `amendment_entitlement` differs from
     `not_authorized_by_this_artifact`;
   - any entry surfacing optimization posture without explicit descriptive support
     basis;
   - any entry laundering mutation, scheduling, release-gating, or settlement
     authority from diagnostic signals.
5. Accepted and reject fixtures that prove at least:
   - accepted canonical register over one bounded snapshot and one bounded source set;
   - reject missing support basis;
   - reject source artifact ref outside declared source set;
   - reject cross-artifact snapshot/source-scope mismatch;
   - reject cross-surface cluster without explicit member carrier;
   - reject amendment-entitlement laundering;
   - reject unresolved finding scope.
6. Tests covering at least:
   - schema/model validation;
   - deterministic replay over committed accepted and rejected fixtures;
   - authoritative/mirrored schema export parity;
   - cross-artifact binding against released `V45-A` through `V45-D` fixtures;
   - bounded vocabulary enforcement;
   - fail-closed authority-laundering rejection.

## Acceptance Gates

Accept this slice only if:

1. canonical `repo_optimization_register@1` compiles deterministically over one
   bounded snapshot and one bounded source set;
2. the artifact binds cleanly to released `V45-A` through `V45-D` descriptive
   surfaces over the same snapshot identity with explicit artifact-local
   source-scope compatibility;
3. every row preserves explicit descriptive-finding versus optimization-candidate
   separation;
4. every row preserves explicit non-authorizing amendment-entitlement posture;
5. `cross_surface_cluster` rows, when present, carry explicit cluster members and
   resolvable member refs;
6. mixed findings remain representable through optional bounded secondary tags rather
   than being flattened into one primary label only;
7. fail-closed laws reject unsupported optimization claims, missing support basis,
   malformed scope refs, and authority laundering;
8. schema export parity and committed fixture replay pass;
9. scoped Python tests cover the released extraction/model surface.

Do not accept this slice if:

- the register collapses diagnostic findings and amendment entitlement into one field;
- hotspot or consolidation rows imply mutation permission by default;
- priority posture is overread as scheduling or release-gating authority;
- bound descriptive references drift across snapshot identity or source-scope
  compatibility posture;
- `cross_surface_cluster` appears without an explicit member carrier;
- source artifact refs are textual only and not source-set-membership checked;
- the first release widens into recursive-governance binding or auto-mutation.

## Local Gate

- run targeted repo-description checks for the changed Python surface;
- run `make arc-start-check ARC=104` while the bundle remains docs-only;
- do not treat this starter bundle as a substitute for the Python lane once source code
  changes begin.
