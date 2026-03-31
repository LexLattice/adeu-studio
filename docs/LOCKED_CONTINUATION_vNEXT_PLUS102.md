# Locked Continuation vNext+102

Status: `V45-C` implementation contract for bounded released-surface hardening
(`100-bis` corrective follow-up).

## V102 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45c_repo_arc_dependency_register_hardening_contract@1",
  "target_arc": "vNext+102",
  "target_path": "V45-C",
  "target_scope": "released_v45c_dependency_register_hardening_over_released_v45a_and_v45c_descriptive_baseline",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_to_V42_released_stack_plus_V45-A_and_V45-C_released_descriptive_surfaces_on_main",
  "governing_stack_consumption_mode": "corrective_descriptive_hardening_not_silent_rewrite_of_released_v45c_surface",
  "dependency_register_schema": "repo_arc_dependency_register@2",
  "released_v45c_surface_consumption_required": true,
  "released_v45c_surface_not_silently_rewritten_required": true,
  "released_v45c_path_order_override_note_required": true,
  "register_scope_not_repo_dependency_graph_required": true,
  "repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "source_set_binding_required": true,
  "source_set_hash_required": true,
  "top_level_extraction_posture_required": true,
  "top_level_extraction_method_required": true,
  "bounded_vocabulary_note_required": true,
  "entry_derivation_posture_required": true,
  "entry_derivation_method_required": true,
  "edge_derivation_posture_required": true,
  "edge_derivation_method_required": true,
  "entry_and_edge_source_artifact_refs_required": true,
  "source_artifact_ref_membership_within_source_set_required": true,
  "blocker_projection_consistency_required": true,
  "explicit_cycle_posture_required": true,
  "explicit_cycle_detection_scope_required": true,
  "pending_list_posture_definition_required": true,
  "undefined_cross_family_vocabulary_rejected": true,
  "supports_all_three_way_claim_field_forbidden": true,
  "authority_posture_non_promotional_required": true,
  "scheduling_priority_entitlement_forbidden": true,
  "auto_mutation_or_auto_planning_resolution_forbidden": true,
  "whole_repo_symbol_graph_release_deferred": true,
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

- Arc label: `vNext+102`
- Family label: `V45-C`
- Scope label: bounded hardening of the released open arc/slice dependency register

## Objective

Release the bounded `V45-C` corrective lane by materializing one canonical
`repo_arc_dependency_register@2` artifact that:

- preserves the released dependency-register seam rather than reopening it wholesale;
- makes provenance, epistemic posture, and cycle posture explicit and inspectable;
- sharpens the object boundary between planning/open-arc dependency posture and the
  later code dependency graph;
- fails closed on missing provenance anchors, missing derivation posture, cycle-posture
  contradictions, or undefined vocabulary laundering.

This slice is released-surface hardening over one bounded descriptive seam, not symbol
catalog release, code dependency-graph release, or mutation authority.

## Frozen Implementation Decisions

1. Corrective-release strategy:
   - `vNext+102` consumes the released `repo_arc_dependency_register@1` seam as
     historical baseline context;
   - the corrective release should emit `repo_arc_dependency_register@2` rather than
     silently rewriting the released `@1` surface in place.
   - this bundle is the numeric stand-in for the conceptually earlier `100-bis`
     corrective follow-up while current arc-bundle tooling remains numeric-only.
   - released `@1` fixtures remain historical evidence only, while deterministic replay
     and schema parity expectations are version-local to the corrected `@2` surface.
2. Path-order strategy:
   - `V45-C` was legitimately pulled forward ahead of `V45-B` because open-arc planning
     dependency visibility did not require released symbol-catalog outputs;
   - `V45-B` remains the broader next widening seam for code-level self-description;
   - `vNext+102` is a bounded hardening follow-up, not a reclassification of `V45-B`.
3. Provenance strategy:
   - each emitted artifact must bind to one repo-visible snapshot identity, one explicit
     source set, and one explicit source-set hash;
   - open-arc entries and dependency edges must each carry explicit source artifact refs
     plus explicit derivation posture and derivation method.
   - every `source_artifact_ref` must resolve inside the declared `source_set`, not
     outside it.
4. Epistemic-posture strategy:
   - extraction and derivation posture must be inspectable rather than hidden behind
     generic evidence lists;
   - consumers must be able to distinguish observed, deterministic, or inferred claims
     inside the dependency register.
5. Projection-consistency strategy:
   - `blocker_arc_ids` and `blocked_by_arc_ids` may remain as entry-level projections,
     but they must reconcile exactly with the incoming dependency-edge subset whose
     `dependency_strength = hard` and `dependency_status = unresolved`;
   - inconsistent blocker projections are invalid.
6. Cycle strategy:
   - cycle posture and cycle detection scope must be explicit at the artifact level;
   - cycles may not appear without that posture being represented clearly.
7. Vocabulary-hygiene strategy:
   - undefined or cross-family vocabulary may not harden implicitly;
   - `supports_all_three_way_claim` must not survive into the corrected surface unless
     separately defined by a bounded released doctrine, which this slice does not
     introduce.
8. Object-boundary strategy:
   - the corrected artifact remains a planning/open-arc dependency register;
   - it may not present itself as the later `repo_dependency_graph` code-self-description
     surface.
9. Anti-overreach strategy:
   - dependency-register outputs remain descriptive constraints only;
   - no scheduling-priority entitlement, plan-resolution entitlement, or mutation
     entitlement may be minted here.

## Bounded Vocabulary Note

The first corrective release should freeze bounded starter vocabularies for the new
posture and method fields rather than leaving them to implementation taste.

The intended bounded starter vocabularies are:

- `extraction_posture` and `derivation_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `extraction_method` and `derivation_method`:
  - `direct_source_parse`
  - `deterministic_projection`
  - `bounded_inference_rule`
  - `adjudicated_policy`
- `cycle_posture`:
  - `cycles_forbidden`
  - `cycles_present_with_explicit_binding`
- `cycle_detection_scope`:
  - `hard_unresolved_edges_only`
  - `all_declared_edges`
- `pending_list_posture`:
  - `machine_enforced_open_arc_register`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent vocabulary creep.

## Required Deliverables

1. New typed corrective dependency surface:
   - canonical `repo_arc_dependency_register@2` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic dependency-compile entrypoint(s) that:
   - consume one bounded repo snapshot and one declared arc/slice source set;
   - derive typed open-arc entries and typed dependency edges with explicit provenance
     posture;
   - emit explicit pending-list posture, explicit cycle posture, and typed evidence
     refs;
   - fail closed on missing provenance anchors, contradictory status posture, blocker
     projection drift, undefined vocabulary, or authority overreach markers.
3. Top-level schema anchors for `repo_arc_dependency_register@2`:
   - `schema`
   - `repo_arc_dependency_register_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `source_set`
   - `source_set_hash`
   - `register_scope`
   - `pending_list_posture`
   - `cycle_posture`
   - `cycle_detection_scope`
   - `dependency_policy_ref`
   - `dependency_policy_hash`
   - `extraction_posture`
   - `extraction_method`
   - `open_arc_entries`
   - `dependency_edges`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per open arc entry anchors:
     - `arc_id`
     - `family_path`
     - `phase_status`
     - `authority_layer`
     - `readiness_posture`
     - `blocker_arc_ids`
     - `blocked_by_arc_ids`
     - `derivation_posture`
     - `derivation_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
   - per dependency edge anchors:
     - `edge_id`
     - `from_arc_id`
     - `to_arc_id`
     - `dependency_kind`
     - `dependency_strength`
     - `dependency_status`
     - `derivation_posture`
     - `derivation_method`
     - `source_artifact_refs`
     - `supporting_evidence_refs`
4. Deterministic laws that fail closed on at least:
   - missing snapshot identity/hash binding;
   - missing or empty source-set binding;
   - missing source-set hash;
   - missing extraction posture or extraction method;
   - any entry or edge missing required derivation posture, derivation method, or source
     artifact refs;
   - any `source_artifact_ref` that falls outside the declared `source_set`;
   - any edge referencing an unknown arc entry;
   - duplicate arc IDs or duplicate edge IDs;
   - any blocker-list projection not exactly reconcilable with the incoming unresolved
     hard-edge subset for that entry;
   - contradictory readiness posture;
   - dependency cycles present without explicit cycle posture and cycle detection scope;
   - undefined pending-list posture;
   - any surviving `supports_all_three_way_claim` field or similar undefined
     cross-family vocabulary;
   - dependency register fields carrying scheduling-priority or mutation-entitlement
     claims as authoritative outcomes;
   - outputs claiming to be the later `repo_dependency_graph` surface.
5. Committed reference fixtures under `apps/api/fixtures/repo_description/vnext_plus102/`:
   - one accepted dependency-register `@2` reference fixture;
   - one rejected fixture with missing source-set provenance;
   - one rejected fixture with missing entry derivation posture;
   - one rejected fixture with missing edge source-artifact refs;
   - one rejected fixture with `source_artifact_ref` outside the declared `source_set`;
   - one rejected fixture with blocker-list / dependency-edge inconsistency;
   - one rejected fixture with missing cycle posture;
   - one rejected fixture with undefined pending-list posture;
   - one rejected fixture retaining `supports_all_three_way_claim`;
   - one rejected fixture with authority-laundering scheduling entitlement claim.
6. Python tests covering:
   - schema/model validation for corrected dependency-register artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for the accepted fixture;
   - rejection of provenance/posture/cycle/vocabulary/authority contradictions.

## Hard Constraints

- `vNext+102` may not reopen or redefine released `V41`, `V42`, `V45-A`, or the
  released `repo_arc_dependency_register@1` contract in place.
- `vNext+102` may not widen into symbol catalog release, code dependency-graph release,
  test-intent matrix release, optimization-register release, or recursive-governance
  binding.
- `vNext+102` must keep dependency outputs descriptive-first and non-promotional.
- `vNext+102` may not treat dependency diagnostics as automatic scheduling authority.
- `vNext+102` may not treat dependency diagnostics as mutation entitlement.
- `vNext+102` outputs must remain snapshot-bound and historical when stale.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- corrective schema release, deterministic compilation hardening, fixture ladder, and
  fail-closed validation are one tightly coupled seam;
- splitting them would create temporary contract drift around the same bounded
  corrective `V45-C` lane.
