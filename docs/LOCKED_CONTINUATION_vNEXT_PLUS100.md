# Locked Continuation vNext+100

Status: `V45-C` implementation contract.

## V100 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45c_repo_arc_dependency_register_contract@1",
  "target_arc": "vNext+100",
  "target_path": "V45-C",
  "target_scope": "open_arc_and_slice_dependency_register_over_released_v45a_descriptive_baseline",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_to_V42_released_stack_plus_V45-A_released_descriptive_surfaces_on_main",
  "governing_stack_consumption_mode": "descriptive_consumption_not_scheduler_or_mutation_authority_minting",
  "dependency_register_schema": "repo_arc_dependency_register@1",
  "descriptive_plane_first_required": true,
  "machine_enforced_pending_list_required": true,
  "open_arc_entry_typing_required": true,
  "dependency_edge_typing_required": true,
  "dependency_status_typing_required": true,
  "dependency_cycle_detection_or_explicit_cycle_flag_required": true,
  "repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "dependency_policy_binding_required": true,
  "dependency_policy_hash_required": true,
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
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md"
}
```

## Slice

- Arc label: `vNext+100`
- Family label: `V45-C`
- Scope label: open arc/slice dependency register over one bounded repo snapshot

## Objective

Release the bounded `V45-C` dependency-register lane by materializing one canonical
`repo_arc_dependency_register@1` artifact that:

- captures open arc/slice entries and typed dependency edges;
- preserves descriptive-first posture over snapshot-bound evidence;
- fails closed on dangling dependencies, contradictory status posture, and authority
  laundering into scheduling/mutation entitlement.

This slice is dependency visibility and constraint surfacing, not auto-scheduling,
auto-resolution, or mutation authority.

## Frozen Implementation Decisions

1. Descriptive-first dependency strategy:
   - register outputs are descriptive constraints over open arc/slice posture;
   - outputs may constrain planning but may not mint scheduling or mutation authority.
2. Snapshot authority strategy:
   - each register emission binds to one explicit repo snapshot identity/hash;
   - stale outputs are historical snapshot-bound evidence, not current planning truth.
3. Dependency modeling strategy:
   - open arcs/slices are represented as typed entries with explicit phase status and
     authority layer posture;
   - dependencies are represented as typed directed edges, not prose-only references.
4. Policy binding strategy:
   - each output binds to one dependency-policy reference plus immutable policy hash;
   - missing policy binding is invalid.
5. Status/consistency strategy:
   - dependency edges must reference known arc entries;
   - blocked/ready posture must be consistent with declared dependencies;
   - cycle posture must be explicit and inspectable.
6. Anti-overreach strategy:
   - register diagnostics may not be treated as execution priority entitlement;
   - register diagnostics may not directly authorize plan closure or code mutation.

## Required Deliverables

1. New typed dependency surface:
   - canonical `repo_arc_dependency_register@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic dependency-compile entrypoint(s) that:
   - consume one bounded repo snapshot and declared arc/slice source-set;
   - derive typed open arc entries and typed dependency edges;
   - emit explicit status posture, blockers, and typed evidence refs;
   - fail closed on dangling refs, contradictory status posture, or authority
     overreach markers.
3. Top-level schema anchors for `repo_arc_dependency_register@1`:
   - `schema`
   - `repo_arc_dependency_register_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `register_scope`
   - `dependency_policy_ref`
   - `dependency_policy_hash`
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
     - `supporting_evidence_refs`
   - per dependency edge anchors:
     - `edge_id`
     - `from_arc_id`
     - `to_arc_id`
     - `dependency_kind`
     - `dependency_strength`
     - `dependency_status`
     - `supports_all_three_way_claim`
     - `supporting_evidence_refs`
4. Deterministic laws that fail closed on at least:
   - missing snapshot identity/hash binding;
   - missing dependency-policy ref/hash binding;
   - any edge referencing an unknown arc entry;
   - duplicate arc IDs or duplicate edge IDs;
   - contradictory readiness posture (for example `ready` while unresolved hard blockers
     are still active);
   - dependency cycles present without explicit cycle posture;
   - dependency register fields carrying scheduling-priority or mutation-entitlement
     claims as authoritative outcomes.
5. Committed reference fixtures under `apps/api/fixtures/repo_description/vnext_plus100/`:
   - one accepted dependency-register reference fixture;
   - one rejected fixture with missing snapshot identity;
   - one rejected fixture with dangling dependency target arc;
   - one rejected fixture with duplicate edge identity;
   - one rejected fixture with unresolved blocker but `ready` posture;
   - one rejected fixture with authority-laundering scheduling entitlement claim.
6. Python tests covering:
   - schema/model validation for dependency-register artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for accepted fixture;
   - rejection of identity/dependency/status/authority contradictions.

## Hard Constraints

- `vNext+100` may not reopen or redefine released `V41`, `V42`, or released `V45-A`
  contracts.
- `vNext+100` may not widen into symbol catalog release, test-intent matrix release,
  optimization-register release, or recursive-governance binding.
- `vNext+100` must keep dependency outputs descriptive-first and non-promotional.
- `vNext+100` may not treat dependency diagnostics as automatic scheduling authority.
- `vNext+100` may not treat dependency diagnostics as mutation entitlement.
- `vNext+100` outputs must remain snapshot-bound and historical when stale.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- dependency schema release, deterministic compilation, fixture ladder, and fail-closed
  validation are one tightly coupled seam;
- splitting them would create temporary contract drift for the same bounded `V45-C`
  lane.
