# Locked Continuation vNext+98

Status: `V42-G4` implementation contract.

## V98 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42g4_arc_behavior_mapping_evidence_bundle_contract@1",
  "target_arc": "vNext+98",
  "target_path": "V42-G4",
  "target_scope": "arc_behavior_mapping_evidence_bundle_over_released_v42_stack",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "governing_released_stack": "V42-A_V42-B_V42-C_V42-D_V42-E_V42-F_V42-G1_V42-G2_V42-G3_released_artifacts",
  "governing_stack_consumption_mode": "workflow_consumption_not_artifact_ladder_redefinition",
  "puzzle_input_bundle_schema": "adeu_arc_puzzle_input_bundle@1",
  "reasoning_run_record_schema": "adeu_arc_reasoning_run_record@1",
  "three_puzzle_harness_record_schema": "adeu_arc_three_puzzle_harness_record@1",
  "scorecard_manifest_schema": "adeu_arc_scorecard_manifest@1",
  "submission_execution_record_schema": "adeu_arc_submission_execution_record@1",
  "behavior_evidence_bundle_schema": "adeu_arc_behavior_evidence_bundle@1",
  "local_first_foundation_required": true,
  "three_puzzle_harness_binding_required": true,
  "canonical_selection_order_carry_required": true,
  "exact_three_per_puzzle_behavior_entries_required": true,
  "per_puzzle_behavior_mapping_required": true,
  "cross_puzzle_pattern_synthesis_required": true,
  "cross_puzzle_pattern_support_binding_required": true,
  "cross_puzzle_pattern_full_support_posture_required": true,
  "typed_failure_mode_catalog_required": true,
  "typed_failure_mode_taxonomy_required": true,
  "typed_claim_posture_register_required": true,
  "claim_posture_target_support_limitation_required": true,
  "observed_vs_inferred_claim_distinction_required": true,
  "authority_boundary_binding_required": true,
  "authority_boundary_register_structured_required": true,
  "cross_puzzle_config_consistency_carry_required": true,
  "narrative_non_authoritative_required": true,
  "deterministic_replay_scope_clarified_required": true,
  "deterministic_fresh_model_reexecution_claim_forbidden": true,
  "post_hoc_claim_laundering_rejected": true,
  "behavior_overclaim_laundering_rejected": true,
  "new_semantic_solver_authority_minting_forbidden": true,
  "benchmark_tournament_orchestration_execution_deferred": true,
  "api_web_operator_surfaces_deferred": true,
  "generalized_multi_agent_orchestration_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v25.md"
}
```

## Slice

- Arc label: `vNext+98`
- Family label: `V42-G4`
- Scope label: ARC behavior mapping and evidence bundle over released
  `V42-A`..`V42-G3` stack

## Objective

Release the bounded behavior-mapping evidence lane by synthesizing one canonical
three-puzzle behavior evidence bundle from released `V42-G3` harness outputs, while
preserving typed authority boundaries, deterministic replay posture, and fail-closed
rejection of narrative or claim laundering.

This slice is workflow consumption over released artifacts, not ladder redefinition.

## Frozen Implementation Decisions

1. Governing stack strategy:
   - released `V42-A`..`V42-G3` remain authoritative doctrine;
   - `V42-G4` consumes those surfaces and may not redefine their semantics.
2. Input authority strategy:
   - each behavior evidence bundle must bind to one released
     `adeu_arc_three_puzzle_harness_record@1` and its referenced released
     puzzle/run/eval surfaces;
   - ambient prompt-authored puzzle/run selection is invalid.
3. Mapping strategy:
   - behavior mapping is per-puzzle first, then cross-puzzle synthesis;
   - mapped behavior surfaces must remain traceable to typed upstream refs;
   - exactly three per-puzzle behavior entries are required in canonical order (no
     omissions, no extras).
4. Failure-mode strategy:
   - failure modes must be represented as typed catalog entries with explicit evidence
     refs and puzzle/run provenance;
   - failure-mode taxonomy must be stable and typed (`failure_mode_id`,
     `failure_mode_kind`, `failure_mode_scope`, `evidence_refs`, `claim_posture`);
   - open-text failure claims without typed anchors are invalid.
5. Claim-posture strategy:
   - claims must be carried through typed claim-posture registers with explicit
     uncertainty/constraint posture;
   - claim entries must include typed claim target, supporting refs, and limitation
     scope;
   - observed per-puzzle behavior claims and inferred cross-puzzle tendency claims must
     be explicitly distinguished in typed surfaces;
   - leaderboard-readiness, universal-necessity, or blanket competitiveness laundering
     is invalid.
6. Authority-boundary strategy:
   - narrative synthesis is descriptive only and may not override typed upstream
     authority surfaces;
   - authority boundary register must be explicitly structured into typed authoritative
     vs descriptive vs deferred-claim surfaces;
   - evidence authority remains with released typed artifacts and evidence refs.
7. Cross-puzzle support and consistency strategy:
   - every cross-puzzle pattern entry must carry explicit support refs to one or more
     per-puzzle behavior entries plus typed evidence refs;
   - any pattern claiming a shared tendency across all three puzzles must carry support
     coverage for all three;
   - cross-puzzle synthesis posture must carry and respect released harness/run config
     consistency surfaces.
8. Deterministic replay scope strategy:
   - deterministic replay in `V42-G4` means deterministic derivation/validation of
     behavior evidence bundle artifacts over fixed emitted upstream artifacts and fixed
     evidence refs;
   - this slice does not claim deterministic fresh model re-execution.
9. Anti-laundering strategy:
   - post-hoc narrative upgrades that add unsupported capability claims are invalid;
   - behavior conclusions must fail closed when required evidence anchors are missing;
   - `V42-G4` may not mint new semantic solver authority, puzzle-rule authority, or
     capability authority absent from upstream typed artifacts.
10. Local-first and widening strategy:
   - this slice remains local and bounded to the released three-puzzle harness posture;
   - benchmark-tournament/API/generalized orchestration widenings remain deferred.

## Required Deliverables

1. New typed behavior-evidence surface:
   - canonical `adeu_arc_behavior_evidence_bundle@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic behavior-synthesis entrypoint(s) that:
   - consume one released three-puzzle harness record and its typed upstream refs;
   - derive per-puzzle behavior mapping entries and cross-puzzle pattern synthesis;
   - emit typed failure-mode catalog and typed claim-posture register surfaces;
   - fail closed on missing anchors, authority-boundary contradictions, or narrative
     laundering posture.
3. Top-level schema anchors for `adeu_arc_behavior_evidence_bundle@1`:
   - `schema`
   - `behavior_evidence_bundle_id`
   - `harness_record_id`
   - `harness_run_id`
   - `puzzle_input_bundle_id`
   - `selection_register_id`
   - `selection_register_hash`
   - `selected_puzzle_ids`
   - `canonical_puzzle_order`
   - `per_puzzle_behavior_entries`
   - `cross_puzzle_pattern_entries`
   - `failure_mode_catalog`
   - `claim_posture_register`
   - `authority_boundary_register`
   - `deterministic_replay_scope_note`
   - `behavior_summary`
   - `evidence_refs`
   - per cross-puzzle pattern entry anchors:
     - `pattern_id`
     - `pattern_kind`
     - `support_puzzle_ids`
     - `support_behavior_entry_refs`
     - `support_evidence_refs`
     - `pattern_claim_posture`
     - `support_posture`
   - per failure-mode catalog entry anchors:
     - `failure_mode_id`
     - `failure_mode_kind`
     - `failure_mode_scope`
     - `evidence_refs`
     - `claim_posture`
   - per claim-posture entry anchors:
     - `claim_id`
     - `claim_target_ref`
     - `supporting_refs`
     - `posture_kind`
     - `limitation_scope`
     - `claim_inference_kind`
   - per authority-boundary register anchors:
     - `authoritative_surface_refs`
     - `descriptive_only_surface_refs`
     - `deferred_claim_refs`
     - `boundary_violation_flags`
   - per puzzle behavior entry anchors:
     - `puzzle_index`
     - `puzzle_id`
     - `reasoning_run_record_ref`
     - `local_eval_ref`
     - `scorecard_manifest_ref`
     - `submission_execution_record_ref`
     - `behavior_signal_refs`
     - `mapped_failure_mode_ids`
     - `claim_posture`
4. Deterministic laws that fail closed on at least:
   - any behavior bundle not bound to one released harness record with exactly three
     canonical puzzle entries;
   - any behavior bundle containing anything other than exactly three canonical
     per-puzzle behavior entries (including omitted-entry laundering);
   - any puzzle behavior entry not aligned with released canonical puzzle order;
   - any behavior entry missing required puzzle/run/eval typed refs;
   - any cross-puzzle pattern entry missing explicit support puzzle IDs, support
     behavior-entry refs, or support evidence refs;
   - any cross-puzzle pattern that claims all-three shared tendency without support for
     all three canonical puzzle IDs;
   - any failure-mode catalog entry missing stable typed taxonomy fields or missing typed
     evidence anchors;
   - any claim-posture entry missing typed target/support/limitation fields, or missing
     explicit observed-vs-inferred claim distinction;
   - any claim-posture entry making unsupported readiness/necessity claims;
   - any cross-puzzle inferred tendency claim represented without explicit support
     bindings to per-puzzle observed behavior entries;
   - any authority-boundary contradiction where narrative content overrides typed
     upstream surfaces;
   - any cross-puzzle synthesis claim that overreaches across heterogeneous config
     posture without explicit typed limitation posture;
   - any deterministic replay claim depending on fresh model re-execution rather than
     fixed emitted artifacts/evidence;
   - any behavior summary content presented as authoritative over typed behavior
     surfaces;
   - any behavior bundle that mints new semantic solver/puzzle-rule/capability authority
     absent from upstream typed artifacts.
5. Committed reference fixtures under `apps/api/fixtures/arc_agi/vnext_plus98/`:
   - one accepted behavior evidence bundle bound to the released v97 harness fixture;
   - one rejected bundle with harness-binding mismatch;
   - one rejected bundle with canonical-order drift in per-puzzle behavior entries;
   - one rejected bundle with cross-puzzle pattern unsupported by referenced per-puzzle
     behavior entries;
   - one rejected bundle with missing typed failure-mode evidence anchors;
   - one rejected bundle with unsupported readiness/necessity claim laundering;
   - one rejected bundle with authority-boundary contradiction;
   - one rejected bundle with missing per-puzzle upstream refs.
6. Python tests covering:
   - schema/model validation for behavior evidence artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for accepted behavior bundle fixture;
   - rejection of harness/order/identity/anchor/claim/authority contradictions and
     unsupported cross-puzzle generalization posture.

## Hard Constraints

- `vNext+98` may not reopen or redefine released `V41` or released `V42-A`..`V42-G3`
  contracts.
- `vNext+98` may not widen into benchmark tournament orchestration execution, API/web
  operator routes, or generalized multi-agent/multi-benchmark orchestration.
- `vNext+98` must keep behavior synthesis bound to released typed harness/puzzle/run/eval
  inputs; ambient prompt-authored authority claims are invalid.
- `vNext+98` must preserve fail-closed posture for missing evidence anchors, authority
  boundary contradictions, and claim-posture laundering.
- `vNext+98` must keep cross-puzzle pattern claims explicitly support-bound to per-puzzle
  observed behavior entries, with all-three support required for all-three claims.
- `vNext+98` must keep failure-mode taxonomy and claim-posture/authority-boundary
  registers typed, inspectable, and stable for deterministic replay.
- `vNext+98` must carry and respect cross-puzzle config-consistency posture when
  synthesizing cross-puzzle tendencies.
- `vNext+98` deterministic replay claims must be limited to fixed emitted artifacts plus
  fixed evidence refs.
- `vNext+98` may not treat narrative behavior summary fields as authoritative over typed
  behavior identity and evidence surfaces.
- `vNext+98` may not mint new semantic solver authority, puzzle-rule authority, or
  capability authority absent from upstream typed artifacts.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- behavior-bundle schema release, deterministic synthesis wiring, fixture ladder, and
  fail-closed validation are one tightly coupled seam;
- splitting these across multiple PRs would create temporary contract drift for the same
  bounded `V42-G4` lane.
