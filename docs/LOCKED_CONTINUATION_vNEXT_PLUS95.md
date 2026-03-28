# Locked Continuation vNext+95

Status: `V42-G1` implementation contract.

## V95 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42g1_arc_local_puzzle_ingest_freeze_contract@1",
  "target_arc": "vNext+95",
  "target_path": "V42-G1",
  "target_scope": "arc_local_puzzle_ingest_and_freeze_over_released_v42_stack",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "governing_released_stack": "V42-A_V42-B_V42-C_V42-D_V42-E_V42-F_released_artifacts",
  "governing_stack_consumption_mode": "workflow_consumption_not_direct_lineage_input",
  "authoritative_puzzle_input_source_required": true,
  "authoritative_selection_register_required": true,
  "local_first_foundation_required": true,
  "workflow_consumption_lane_required": true,
  "artifact_ladder_redefinition_forbidden": true,
  "authoritative_puzzle_source_binding_required": true,
  "puzzle_source_kind_enum_required": true,
  "puzzle_source_kind_precedence_policy_required": true,
  "predeclared_puzzle_selection_register_required": true,
  "selection_register_typed_identity_required": true,
  "deterministic_puzzle_freeze_required": true,
  "puzzle_identity_hash_binding_required": true,
  "bundle_identity_hash_required": true,
  "canonical_bundle_ordering_required": true,
  "puzzle_provenance_refs_required": true,
  "bounded_initial_puzzle_count_required": true,
  "three_puzzle_reference_set_required": true,
  "duplicate_puzzle_identity_rejection_required": true,
  "retrospective_puzzle_swap_forbidden": true,
  "deterministic_replay_over_frozen_local_payloads_required": true,
  "live_external_fetch_determinism_claim_forbidden": true,
  "local_online_authority_separation_required": true,
  "summary_non_authoritative_required": true,
  "benchmark_tournament_orchestration_execution_deferred": true,
  "api_web_operator_surfaces_deferred": true,
  "generalized_multi_agent_orchestration_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v25.md"
}
```

## Slice

- Arc label: `vNext+95`
- Family label: `V42-G1`
- Scope label: ARC local puzzle ingest and deterministic freeze over released `V42-A`..`V42-F` stack

## Objective

Release the first bounded operationalization lane over `V42-A`..`V42-F` by introducing a
canonical local puzzle-ingest and freeze surface that makes a fixed three-puzzle
ARC-AGI-3 reference cohort replayable with explicit authority, provenance, and identity
binding.

This slice is about workflow consumption of the released stack, not artifact-ladder
redefinition.

## Frozen Implementation Decisions

1. Governing stack strategy:
   - released `V42-A`..`V42-F` artifacts are governing control-plane doctrine for this
     slice;
   - `V42-G1` does not treat `V42-A`..`V42-F` as direct lineage input artifacts.
2. Puzzle input authority strategy:
   - puzzle input authority is carried by typed `source_kind` + `source_ref` + frozen
     local payload evidence;
   - allowed `source_kind` values in this slice:
     - `official_toolkit_local_export`
     - `repo_frozen_fixture`
     - `approved_imported_local_copy`
   - open-text source-kind values are invalid.
3. Source precedence strategy:
   - when multiple candidate sources exist for the same puzzle identity, precedence must
     be explicit and deterministic:
     - `repo_frozen_fixture`
     - `official_toolkit_local_export`
     - `approved_imported_local_copy`
4. Selection register strategy:
   - one typed selection register is authoritative for the initial cohort;
   - selection register must carry:
     - `selection_register_id`
     - `selection_register_hash`
     - `selection_basis`
     - `selected_puzzle_ids`
     - `no_retrospective_swap_posture`
   - retrospective puzzle swap is invalid.
5. Canonical ordering strategy:
   - bundle puzzle order must exactly follow declared selection order in the selection
     register;
   - bundle identity hash must bind canonical order plus per-puzzle identities.
6. Deterministic replay strategy:
   - deterministic replay in `V42-G1` means deterministic derivation and validation over
     fixed frozen local puzzle payloads and fixed provenance evidence;
   - this slice does not claim deterministic behavior of live external fetch operations.

## Required Deliverables

1. New typed local ingest/freeze surface:
   - canonical `adeu_arc_puzzle_input_bundle@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic ingest entrypoints that:
   - bind each puzzle to an explicit bounded `source_kind` enum value and typed
     `source_ref`;
   - normalize and freeze puzzle payload into deterministic local representation;
   - compute and carry per-puzzle identity hashes and one bundle identity hash over
     canonical bundle order;
   - fail closed on malformed source, missing provenance, or hash mismatches.
3. Fixed three-puzzle selection register under
   `apps/api/fixtures/arc_agi/vnext_plus95/` that includes:
   - `selection_register_id`;
   - `selection_register_hash`;
   - declared selection basis;
   - declared puzzle IDs for the initial cohort;
   - explicit no-retrospective-swap posture.
4. Top-level schema anchors for `adeu_arc_puzzle_input_bundle@1`:
   - `schema`
   - `puzzle_input_bundle_id`
   - `selection_register_id`
   - `selection_register_ref`
   - `selection_register_hash`
   - `selection_basis`
   - `source_profile`
   - `source_precedence_policy`
   - `selected_puzzle_ids`
   - `canonical_puzzle_order`
   - `puzzle_entries`
   - `bundle_identity_hash`
   - `no_retrospective_swap_posture`
   - `provenance_refs`
   - `summary_non_authoritative`
   - `evidence_refs`
   - per puzzle entry anchors:
     - `puzzle_input_id`
     - `puzzle_id`
     - `source_kind`
     - `source_ref`
     - `normalized_payload_ref`
     - `normalized_payload_hash`
     - `puzzle_identity_hash`
     - `provenance_refs`
5. Deterministic laws that fail closed on at least:
   - any bundle not bound to one declared typed selection register;
   - any bundle containing anything other than exactly three selected puzzles;
   - any duplicate puzzle identity within the same bundle;
   - any puzzle entry with `source_kind` outside released enum values;
   - any puzzle entry missing typed `source_kind` or typed `source_ref`;
   - any puzzle identity hash mismatch against normalized payload;
   - any bundle identity hash mismatch against canonical puzzle order and entry hashes;
   - any puzzle ordering that differs from declared selection-register order;
   - any undeclared puzzle or retrospective swap against the frozen selection register;
   - any replay path that depends on live external fetch behavior instead of frozen local
     payload evidence.
6. Committed reference fixtures under `apps/api/fixtures/arc_agi/vnext_plus95/`:
   - one accepted canonical puzzle bundle containing exactly three selected puzzles;
   - one rejected bundle with missing provenance refs;
   - one rejected bundle with per-puzzle identity-hash mismatch;
   - one rejected bundle with bundle-identity-hash mismatch;
   - one rejected bundle with non-declared/retrospective puzzle swap;
   - one rejected bundle with duplicate puzzle identity.
7. Python tests covering:
   - schema/model validation for puzzle input bundle artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay from the accepted fixture;
   - rejection of missing provenance, source-kind drift, hash mismatch, duplicate
     identity, and retrospective swap posture.

## Hard Constraints

- `vNext+95` may not reopen or redefine released `V41` or released `V42-A`..`V42-F`
  contracts.
- `vNext+95` may not widen into reasoning-agent execution orchestration (`V42-G2`), local
  multi-puzzle run orchestration (`V42-G3`), or behavior evidence synthesis (`V42-G4`).
- `vNext+95` may not ship benchmark tournament orchestration execution, API/web operator
  routes, or generalized multi-agent/multi-benchmark orchestration.
- `vNext+95` must keep puzzle `source_kind` bounded to released enum values and reject
  open-text source authority claims.
- `vNext+95` must treat puzzle-source authority and puzzle-selection register as typed
  inputs; prompt-authored ambient selection is invalid.
- `vNext+95` must keep selection register identity surfaces typed and stable
  (`selection_register_id`, `selection_register_hash`).
- `vNext+95` must bind bundle identity hash to canonical selection order plus per-puzzle
  hashes.
- `vNext+95` may not reorder accepted puzzles outside the declared selection register
  order.
- `vNext+95` must fail closed when source/provenance/identity fields are missing or
  contradictory.
- `vNext+95` deterministic replay may not depend on live external fetch behavior.
- `vNext+95` may not treat narrative summary fields as authoritative over typed source,
  selection, and identity surfaces.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- puzzle-source binding, deterministic freeze logic, fixture ladder, and fail-closed
  validation are one tightly coupled seam;
- splitting these across multiple PRs would create temporary contract drift for the same
  bounded `V42-G1` lane.
