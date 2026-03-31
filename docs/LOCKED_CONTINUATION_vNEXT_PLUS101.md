# Locked Continuation vNext+101

Status: `V45-B` implementation contract.

## V101 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45b_repo_symbol_catalog_dependency_graph_contract@1",
  "target_arc": "vNext+101",
  "target_path": "V45-B",
  "target_scope": "repo_symbol_catalog_and_typed_dependency_graph_over_released_v45a_v45c_descriptive_baseline",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_to_V42_released_stack_plus_V45-A_and_V45-C_released_descriptive_surfaces_on_main",
  "governing_stack_consumption_mode": "descriptive_consumption_not_refactor_or_normative_authority_minting",
  "repo_symbol_catalog_schema": "repo_symbol_catalog@1",
  "repo_dependency_graph_schema": "repo_dependency_graph@1",
  "descriptive_plane_first_required": true,
  "bounded_python_source_surface_required": true,
  "repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "source_set_binding_required": true,
  "source_set_hash_required": true,
  "top_level_extraction_posture_required": true,
  "top_level_extraction_method_required": true,
  "typed_symbol_entry_required": true,
  "typed_dependency_edge_required": true,
  "typed_endpoint_kind_model_required": true,
  "external_or_out_of_scope_dependency_representation_required": true,
  "cross_artifact_snapshot_source_consistency_required": true,
  "symbol_kind_required": true,
  "symbol_identity_canonicalization_strategy_required": true,
  "symbol_role_classification_posture_required": true,
  "symbol_role_classification_method_required": true,
  "symbol_source_artifact_refs_required": true,
  "dependency_posture_required": true,
  "dependency_derivation_posture_required": true,
  "dependency_derivation_method_required": true,
  "dependency_source_artifact_refs_required": true,
  "bounded_vocabulary_note_required": true,
  "dangling_symbol_ref_rejection_required": true,
  "authority_posture_non_promotional_required": true,
  "automatic_refactor_or_mutation_entitlement_forbidden": true,
  "test_intent_matrix_release_deferred": true,
  "optimization_register_release_deferred": true,
  "recursive_governance_binding_deferred": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "source_architecture_doc": "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
  "decomposition_doc": "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
}
```

## Slice

- Arc label: `vNext+101`
- Family label: `V45-B`
- Scope label: bounded repo symbol catalog and typed dependency graph over one repo
  snapshot

## Objective

Release the bounded `V45-B` code-self-description lane by materializing:

- one canonical `repo_symbol_catalog@1`;
- one canonical `repo_dependency_graph@1`;

while preserving snapshot identity, explicit source-set posture, descriptive-only
authority boundaries, cross-artifact consistency, and fail-closed rejection of dangling
refs, untyped boundary endpoints, or refactor-entitlement laundering.

This slice is descriptive code-structure compilation, not optimization entitlement,
test-intent inference, or recursive-governance binding.

## Frozen Implementation Decisions

1. Descriptive-first strategy:
   - `V45-B` emits typed code-symbol and typed dependency-graph surfaces only;
   - outputs may constrain later planning but may not mint refactor, scheduling, or
     mutation authority.
2. Path-order strategy:
   - `V45-A` and `V45-C` remain authoritative released descriptive baselines on `main`;
   - `V45-B` is the next widening because later `V45-D` through `V45-F` need typed
     code-level self-description in addition to released schema-registry and
     dependency-register surfaces.
3. Source authority strategy:
   - all emitted artifacts must bind to one explicit repo-visible snapshot identity and
     one explicit bounded Python source set;
   - both artifacts must also bind one explicit source-set hash and one explicit
     extraction posture/method pair;
   - stale-snapshot semantics must be explicit rather than implied;
   - outputs are valid for the bound snapshot only and become historical evidence when
     stale.
4. Language-surface strategy:
   - the first `V45-B` release stays bounded to Python source surfaces only;
   - multi-language widening remains deferred.
5. Symbol modeling strategy:
   - symbol entries must be typed and inspectable;
   - each symbol row must carry stable identity, module path, qualified name, symbol
     kind, bounded role-classification posture, and explicit source artifact refs;
   - the first release should derive `symbol_id` deterministically from
     `module_path + qualname + symbol_kind` or an equivalent explicitly documented
     canonicalization rule emitted by the same artifact family;
   - naming-only role claims are insufficient.
6. Dependency-graph strategy:
   - dependency edges must be represented as typed refs over the bound source set, not
     prose-only statements;
   - the first `V45-B` release should use a typed mixed graph rather than silently
     collapsing all endpoints into one string namespace;
   - every endpoint must therefore carry an explicit endpoint-kind model that
     distinguishes at least:
     - internal symbol refs;
     - internal module-boundary refs;
     - external or out-of-scope dependency refs;
   - dependency posture must be explicit and inspectable;
   - edge derivation posture/method and source artifact refs must be explicit.
7. Cross-artifact consistency strategy:
   - `repo_symbol_catalog@1` and `repo_dependency_graph@1` must reconcile over the same
     snapshot identity/hash and the same source-set identity/hash;
   - every internal graph endpoint must resolve against the emitted symbol catalog or an
     explicitly declared internal module-boundary namespace;
   - every out-of-scope target must be represented through valid typed boundary or
     external endpoint kinds rather than as an untyped dangling string.
8. Anti-overreach strategy:
   - overlap, hotspot, or strong-dependency findings may not be treated as refactor
     entitlement;
   - `V45-B` may not claim test intent, optimization priority, or recursive-governance
     authority.

## Bounded Vocabulary Note

The first `V45-B` release should freeze bounded starter vocabularies for the new typed
fields rather than leaving them to implementation taste.

The intended bounded starter vocabularies are:

- `symbol_kind`:
  - `module`
  - `class`
  - `function`
  - `method`
  - `attribute`
- `role_classification_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `role_classification_method`:
  - `ast_signature`
  - `decorator_or_baseclass_rule`
  - `bounded_inference_rule`
  - `adjudicated_policy`
- `dependency_kind`:
  - `module_import`
  - `symbol_reference`
  - `inheritance`
- `dependency_posture`:
  - `internal_resolved`
  - `boundary_external`
  - `boundary_out_of_scope`
- `dependency_derivation_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `dependency_derivation_method`:
  - `ast_parse`
  - `deterministic_projection`
  - `bounded_inference_rule`
  - `adjudicated_policy`
- `endpoint_kind`:
  - `internal_symbol`
  - `internal_module_boundary`
  - `external_dependency`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent vocabulary creep.

## Required Deliverables

1. New typed descriptive surfaces:
   - canonical `repo_symbol_catalog@1` artifact;
   - canonical `repo_dependency_graph@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic extraction entrypoint(s) that:
   - consume one explicit repo snapshot and one bounded Python source set;
   - derive typed symbol rows and typed dependency edges as one consistent pair of
     outputs;
   - emit explicit source-set hash, top-level extraction posture/method, explicit
     role-classification posture, explicit dependency posture, explicit dependency
     derivation posture/method, and typed evidence refs;
   - fail closed on dangling refs, duplicate identities, malformed source binding,
     cross-artifact drift, untyped boundary endpoints, or authority laundering posture.
3. Top-level schema anchors for `repo_symbol_catalog@1`:
   - `schema`
   - `repo_symbol_catalog_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `source_set`
   - `source_set_hash`
   - `graph_scope`
   - `extraction_posture`
   - `extraction_method`
   - `symbol_entries`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per symbol entry anchors:
     - `symbol_id`
     - `module_path`
     - `qualname`
     - `symbol_kind`
     - `role_classification_posture`
     - `role_classification_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
4. Top-level schema anchors for `repo_dependency_graph@1`:
   - `schema`
   - `repo_dependency_graph_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `source_set`
   - `source_set_hash`
   - `graph_scope`
   - `extraction_posture`
   - `extraction_method`
   - `dependency_edges`
   - `evidence_refs`
   - per dependency edge anchors:
     - `edge_id`
     - `from_ref_kind`
     - `from_ref`
     - `to_ref_kind`
     - `to_ref`
     - `dependency_kind`
     - `dependency_posture`
     - `derivation_posture`
     - `derivation_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
5. Deterministic laws that fail closed on at least:
   - missing snapshot identity/hash binding;
   - missing or empty bounded source set binding;
   - missing source-set hash;
   - missing top-level extraction posture or extraction method;
   - any symbol entry missing required identity/module/kind/posture fields;
   - any symbol entry missing source artifact refs;
   - duplicate symbol IDs or duplicate edge IDs;
   - any catalog/graph pair with mismatched snapshot identity/hash or mismatched
     source-set identity/hash;
   - any dependency edge whose internal endpoint kinds do not resolve against the
     emitted symbol catalog or declared internal module-boundary namespace;
   - any dependency edge carrying an out-of-scope target without valid boundary typing;
   - any dependency edge missing explicit dependency posture, derivation posture,
     derivation method, source artifact refs, or typed evidence refs;
   - symbol/dependency outputs carrying refactor, scheduling, or mutation entitlement as
     authoritative outcomes;
   - outputs overreaching into test-intent or optimization authority posture.
6. Committed reference fixtures under `apps/api/fixtures/repo_description/vnext_plus101/`:
   - one accepted symbol-catalog reference fixture;
   - one accepted dependency-graph reference fixture paired to the same snapshot and
     source-set identity as the accepted symbol-catalog fixture;
   - one rejected symbol-catalog fixture with missing snapshot identity;
   - one rejected dependency-graph fixture with dangling symbol ref;
   - one rejected symbol-catalog fixture with duplicate symbol identity;
   - one rejected dependency-graph fixture with missing dependency posture;
   - one rejected dependency-graph fixture with out-of-scope endpoint lacking valid
     boundary typing;
   - one rejected paired-fixture bundle with mismatched snapshot/source-set identity;
   - one rejected fixture with refactor-entitlement laundering.
7. Python tests covering:
   - schema/model validation for symbol-catalog and dependency-graph artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for accepted fixtures;
   - rejection of identity/source/dependency/authority contradictions;
   - paired catalog/graph consistency over one snapshot/source-set.

## Hard Constraints

- `vNext+101` may not reopen or redefine released `V41`, `V42`, `V45-A`, or `V45-C`
  contracts.
- `vNext+101` may not widen into test-intent matrix release, optimization-register
  release, or recursive-governance binding.
- `vNext+101` must keep outputs descriptive-first and non-promotional.
- `vNext+101` may not treat overlap or hotspot findings as automatic refactor
  entitlement.
- `vNext+101` may not treat dependency findings as scheduling or mutation entitlement.
- `vNext+101` outputs must remain snapshot-bound and historical when stale.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- symbol-catalog schema release, dependency-graph schema release, deterministic
  extraction, fixture ladder, and fail-closed validation are one tightly coupled seam;
- splitting them would create temporary contract drift for the same bounded `V45-B`
  lane.
