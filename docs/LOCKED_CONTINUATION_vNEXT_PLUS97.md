# Locked Continuation vNext+97

Status: `V42-G3` implementation contract.

## V97 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42g3_arc_three_puzzle_local_harness_contract@1",
  "target_arc": "vNext+97",
  "target_path": "V42-G3",
  "target_scope": "arc_three_puzzle_local_harness_over_released_v42_stack",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "governing_released_stack": "V42-A_V42-B_V42-C_V42-D_V42-E_V42-F_V42-G1_V42-G2_released_artifacts",
  "governing_stack_consumption_mode": "workflow_consumption_not_artifact_ladder_redefinition",
  "puzzle_input_bundle_schema": "adeu_arc_puzzle_input_bundle@1",
  "reasoning_run_record_schema": "adeu_arc_reasoning_run_record@1",
  "scorecard_manifest_schema": "adeu_arc_scorecard_manifest@1",
  "submission_execution_record_schema": "adeu_arc_submission_execution_record@1",
  "three_puzzle_harness_record_schema": "adeu_arc_three_puzzle_harness_record@1",
  "local_first_foundation_required": true,
  "exact_three_puzzle_bound_required": true,
  "predeclared_selection_register_required": true,
  "no_retrospective_swap_required": true,
  "canonical_selection_order_required": true,
  "deterministic_harness_orchestration_required": true,
  "per_puzzle_v42g2_stage_evidence_required": true,
  "cross_puzzle_identity_chain_consistency_required": true,
  "cross_puzzle_agent_config_consistency_required": true,
  "config_divergence_explicit_typing_required": true,
  "exact_three_puzzle_entries_required": true,
  "blocked_failed_entry_slot_occupation_required": true,
  "harness_execution_lifecycle_model_required": true,
  "harness_sequence_monotonicity_required": true,
  "harness_sequence_structured_register_required": true,
  "per_puzzle_eval_scorecard_submission_refs_required": true,
  "optional_typed_harness_aggregate_refs_allowed": true,
  "scorecard_submission_presence_posture_required": true,
  "incomplete_entry_laundering_rejection_required": true,
  "deterministic_replay_scope_clarified_required": true,
  "deterministic_fresh_model_reexecution_claim_forbidden": true,
  "harness_fail_closed_required": true,
  "run_summary_non_authoritative_required": true,
  "benchmark_tournament_orchestration_execution_deferred": true,
  "api_web_operator_surfaces_deferred": true,
  "generalized_multi_agent_orchestration_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v25.md"
}
```

## Slice

- Arc label: `vNext+97`
- Family label: `V42-G3`
- Scope label: ARC deterministic three-puzzle local harness over released
  `V42-A`..`V42-G2` stack

## Objective

Release the bounded three-puzzle local harness lane by orchestrating exactly three
predeclared puzzle runs through released `V42-G1` puzzle authority and `V42-G2`
reasoning-run bridge surfaces, while preserving deterministic ordering, identity-chain
continuity, and fail-closed control-plane evidence.

This slice is workflow consumption over released artifacts, not ladder redefinition.

## Frozen Implementation Decisions

1. Governing stack strategy:
   - released `V42-A`..`V42-G2` remain authoritative doctrine;
   - `V42-G3` consumes those surfaces and may not redefine their semantics.
2. Harness bound strategy:
   - one harness run must include exactly three puzzles;
   - the three puzzles must come from one released selection register from
     `adeu_arc_puzzle_input_bundle@1`.
3. Selection authority strategy:
   - selected puzzle IDs and canonical order come from the frozen selection register;
   - retrospective swap, undeclared puzzle insertion, or order drift is invalid.
4. Per-puzzle run strategy:
   - each puzzle run must bind to one released `adeu_arc_reasoning_run_record@1`;
   - each bound run must preserve required `V42-G2` stage occupation posture.
5. Aggregation strategy:
   - per-puzzle entries must carry downstream refs for released `V42-D`/`V42-E`/`V42-F`
     surfaces (`local_eval`, scorecard posture, submission-posture record);
   - harness-level aggregate refs are optional but must be typed and consistent with
     per-puzzle entries when present.
6. Identity-chain and config-consistency strategy:
   - harness records must carry one coherent cross-puzzle identity chain across:
     - harness run identity;
     - puzzle bundle/register identity;
     - per-puzzle input and run identities;
     - environment/session/competition scope refs.
   - harness runs must keep one stable executable setup across all three puzzle entries:
     - `agent_profile_ref`
     - `run_config_ref`
     - `run_config_hash`
     - `prompt_profile_ref` (when prompt profile is used);
   - configuration divergence is valid only when explicitly typed and justified in
     harness surfaces.
7. Harness lifecycle strategy:
   - harness records must always include exactly three puzzle entries in canonical order,
     even when one or more entries terminate in blocked/failed posture;
   - omission of an entry slot while claiming completion is invalid.
8. Harness sequence strategy:
   - `harness_sequence_register` must be a structured monotonic sequence over canonical
     puzzle entries with typed per-step evidence refs;
   - a harness run may not claim ordered execution without this register.
9. Deterministic replay scope strategy:
   - deterministic replay in `V42-G3` means deterministic derivation/validation of the
     harness record over fixed emitted puzzle/run artifacts and fixed evidence refs;
   - this slice does not claim deterministic fresh model re-execution.
10. Anti-widening strategy:
   - this slice is local and bounded to exactly three puzzles;
   - behavior-evidence synthesis widening (`V42-G4`) remains deferred.

## Required Deliverables

1. New typed harness surface:
   - canonical `adeu_arc_three_puzzle_harness_record@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic harness entrypoint(s) that:
   - consume one released puzzle-input bundle and its authoritative selection register;
   - execute exactly three selected puzzles in canonical order through released
     `V42-G2` run bridge entrypoints;
   - materialize exactly three puzzle-entry slots (including blocked/failed outcomes)
     with per-puzzle downstream refs and typed presence posture;
   - optionally emit typed harness-level aggregate refs that are consistency-checked
     against per-puzzle entries;
   - fail closed on selection/order/identity/evidence contradictions.
3. Top-level schema anchors for `adeu_arc_three_puzzle_harness_record@1`:
   - `schema`
   - `three_puzzle_harness_record_id`
   - `harness_run_id`
   - `expected_puzzle_count`
   - `puzzle_input_bundle_id`
   - `selection_register_id`
   - `selection_register_hash`
   - `selected_puzzle_ids`
   - `canonical_puzzle_order`
   - `harness_execution_status`
   - `puzzle_run_entries`
   - `harness_sequence_register`
   - `harness_sequence_entries`
   - `agent_profile_ref`
   - `run_config_ref`
   - `run_config_hash`
   - `prompt_profile_ref`
   - `config_consistency_posture`
   - `aggregated_local_eval_ref`
   - `aggregated_scorecard_posture_ref`
   - `aggregated_submission_posture_ref`
   - `run_summary`
   - `evidence_refs`
   - per harness sequence entry anchors:
     - `sequence_step`
     - `puzzle_index`
     - `puzzle_id`
     - `run_id`
     - `sequence_evidence_refs`
   - per puzzle entry anchors:
     - `puzzle_index`
     - `puzzle_input_id`
     - `puzzle_id`
     - `run_id`
     - `reasoning_run_record_ref`
     - `run_execution_status`
     - `run_terminal_posture`
     - `rollout_presence_posture`
     - `model_id`
     - `agent_profile_ref`
     - `run_config_ref`
     - `run_config_hash`
     - `prompt_profile_ref`
     - `reasoning_effort_observed`
     - `stage_evidence_ref_set`
     - `local_eval_ref`
     - `scorecard_manifest_ref`
     - `scorecard_presence_posture`
     - `submission_execution_record_ref`
     - `submission_presence_posture`
4. Deterministic laws that fail closed on at least:
   - any harness record not bound to one released selection register and exactly three
     selected puzzle IDs;
   - any harness record containing anything other than exactly three canonical
     `puzzle_run_entries`, including omitted-third-run laundering;
   - any duplicate puzzle identity, undeclared puzzle insertion, or retrospective swap;
   - any puzzle order not equal to declared canonical selection order;
   - any puzzle entry missing required `reasoning_run_record_ref` or required stage
     evidence set from `V42-G2`;
   - any puzzle entry missing required `local_eval_ref`, or missing typed
     scorecard/submission presence posture when those refs are absent;
   - any cross-puzzle identity-chain mismatch across bundle/register/puzzle/run refs;
   - any cross-puzzle agent/config identity drift unless explicitly typed as divergent;
   - any missing/non-monotonic structured `harness_sequence_register` or missing
     per-step sequence evidence refs;
   - any contradiction between typed optional harness aggregate refs and per-puzzle
     downstream refs;
   - any deterministic replay claim that depends on fresh model re-execution rather than
     fixed emitted artifacts/evidence;
   - any run summary content presented as authoritative over typed harness surfaces.
5. Committed reference fixtures under `apps/api/fixtures/arc_agi/vnext_plus97/`:
   - one accepted harness record with exactly three selected puzzles in canonical order;
   - one rejected harness record with retrospective puzzle swap;
   - one rejected harness record with canonical-order violation;
   - one rejected harness record with duplicate puzzle identity;
   - one rejected harness record with claimed completion but omitted third puzzle entry;
   - one rejected harness record with per-puzzle run identity-chain mismatch;
   - one rejected harness record with cross-puzzle run-config drift without explicit
     divergence posture;
   - one rejected harness record with missing harness-sequence monotonic evidence;
   - one rejected harness record with aggregated-ref contradiction.
6. Python tests covering:
   - schema/model validation for harness artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for accepted three-puzzle harness fixture;
   - rejection of selection/order/identity/evidence contradictions, incomplete-entry
     laundering, untyped config drift, and aggregation contradictions.

## Hard Constraints

- `vNext+97` may not reopen or redefine released `V41` or released `V42-A`..`V42-G2`
  contracts.
- `vNext+97` may not widen into behavior-evidence synthesis (`V42-G4`), benchmark
  tournament orchestration execution, API/web operator routes, or generalized
  multi-agent/multi-benchmark orchestration.
- `vNext+97` must keep harness selection authority bound to released typed
  puzzle-bundle/selection-register inputs; ambient prompt-authored puzzle selection is
  invalid.
- `vNext+97` must preserve fail-closed posture for selection/order/identity drift and
  missing/non-monotonic harness evidence.
- `vNext+97` must materialize exactly three canonical puzzle-entry slots even when one
  or more puzzle runs terminate blocked/failed.
- `vNext+97` must keep per-puzzle downstream refs explicit: local eval is required;
  scorecard/submission absence must be typed using presence posture fields.
- `vNext+97` must keep cross-puzzle agent/config identity consistent unless explicit
  divergence posture is typed.
- `vNext+97` deterministic replay claims must be limited to fixed emitted artifacts plus
  fixed evidence refs.
- `vNext+97` may not treat narrative run summary fields as authoritative over typed
  harness identity/occupation surfaces.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- harness schema release, deterministic orchestration wiring, fixture ladder, and
  fail-closed validation are one tightly coupled seam;
- splitting these across multiple PRs would create temporary contract drift for the
  same bounded `V42-G3` lane.
