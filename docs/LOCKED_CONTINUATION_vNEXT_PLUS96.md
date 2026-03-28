# Locked Continuation vNext+96

Status: `V42-G2` implementation contract.

## V96 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42g2_arc_reasoning_agent_run_bridge_contract@1",
  "target_arc": "vNext+96",
  "target_path": "V42-G2",
  "target_scope": "arc_reasoning_agent_run_bridge_over_released_v42_stack",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "governing_released_stack": "V42-A_V42-B_V42-C_V42-D_V42-E_V42-F_V42-G1_released_artifacts",
  "governing_stack_consumption_mode": "workflow_consumption_not_artifact_ladder_redefinition",
  "puzzle_input_bundle_schema": "adeu_arc_puzzle_input_bundle@1",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "observation_frame_schema": "adeu_arc_observation_frame@1",
  "hypothesis_frame_schema": "adeu_arc_hypothesis_frame@1",
  "action_proposal_schema": "adeu_arc_action_proposal@1",
  "rollout_trace_schema": "adeu_arc_rollout_trace@1",
  "reasoning_run_record_schema": "adeu_arc_reasoning_run_record@1",
  "local_first_foundation_required": true,
  "single_attempt_bound_required": true,
  "deterministic_replay_scope_clarified_required": true,
  "deterministic_fresh_model_reexecution_claim_forbidden": true,
  "in_band_artifact_emission_required": true,
  "staged_in_band_emission_evidence_required": true,
  "emission_sequence_monotonicity_required": true,
  "post_hoc_artifact_reconstruction_rejected": true,
  "intermediate_surface_occupation_required": true,
  "intermediate_surface_fail_closed_required": true,
  "run_execution_lifecycle_model_required": true,
  "run_terminal_posture_required": true,
  "rollout_presence_posture_required": true,
  "blocked_or_deferred_action_posture_admissible_required": true,
  "attempt_identity_chain_binding_required": true,
  "agent_configuration_identity_binding_required": true,
  "reasoning_effort_semantics_explicit_required": true,
  "branching_visibility_surface_required": true,
  "prompt_only_hidden_branching_non_equivalence_required": true,
  "settlement_posture_carry_required": true,
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

- Arc label: `vNext+96`
- Family label: `V42-G2`
- Scope label: ARC reasoning-agent run bridge over released `V42-A`..`V42-G1` stack

## Objective

Release the first bounded reasoning-agent run bridge over the released ARC participation
stack by introducing one canonical run-record surface that proves in-band occupation of
the ADEU control plane for a single local reasoning attempt over one released puzzle
input, with stage-aware emission evidence instead of artifact-compatible post-hoc
serialization.

This slice is workflow consumption over released artifacts, not ladder redefinition.

## Frozen Implementation Decisions

1. Governing stack strategy:
   - released `V42-A`..`V42-F` plus `V42-G1` remain authoritative governing doctrine;
   - `V42-G2` consumes these surfaces and may not redefine their semantics.
2. Puzzle input authority strategy:
   - each run attempt must bind to one released `adeu_arc_puzzle_input_bundle@1` and one
     selected puzzle entry from its canonical order;
   - prompt-authored ambient puzzle selection is invalid.
3. Deterministic replay scope strategy:
   - deterministic replay in `V42-G2` means deterministic derivation and validation of
     `adeu_arc_reasoning_run_record@1` over fixed emitted artifacts and fixed in-band
     evidence;
   - this slice does not claim deterministic fresh re-execution of reasoning-model
     behavior.
4. In-band ladder occupation strategy:
   - run execution must emit artifact surfaces in-band for at least:
     - `adeu_arc_task_packet@1`
     - `adeu_arc_observation_frame@1`
     - `adeu_arc_hypothesis_frame@1`
     - `adeu_arc_action_proposal@1`
   - action proposal emission is required even for blocked/deferred posture; forced
     committed-action posture is not required;
   - stage-aware emission evidence must be carried per occupied surface plus one
     monotonic `emission_sequence_register`.
5. Rollout and terminal posture strategy:
   - `rollout_trace_ref` is conditional on explicit rollout posture surfaces, not
     implicitly required for every accepted run;
   - run record must carry:
     - `run_terminal_posture`
     - `rollout_presence_posture`
   - `rollout_presence_posture` must be consistent with `rollout_trace_ref` and terminal
     posture.
6. Anti-reconstruction strategy:
   - post-hoc serialization of compatible artifacts without in-band emission evidence is
     invalid;
   - all-at-once compatible dumps without staged evidence ordering are invalid;
   - skipped or malformed intermediate surfaces fail closed.
7. Run lifecycle strategy:
   - `run_execution_status` is bounded by released enum values:
     - `started`
     - `failed_before_task_packet`
     - `task_emitted`
     - `observation_emitted`
     - `hypothesis_emitted`
     - `action_emitted`
     - `rollout_emitted`
     - `blocked_or_deferred`
     - `completed`
   - lifecycle progression must be monotonic and consistent with emitted stage evidence.
8. Attempt identity and configuration strategy:
   - run artifacts must bind to one attempt identity chain:
     - `reasoning_run_record_id`
     - `run_id`
     - `puzzle_input_bundle_id`
     - `selection_register_id`
     - `puzzle_input_id`
     - `puzzle_id`
     - `environment_ref`
     - `session_ref`
     - `competition_scope_ref`
   - run record must carry stable configuration identity anchors:
     - `agent_profile_ref`
     - `run_config_ref`
     - `run_config_hash`
     - `prompt_profile_ref` (when prompt-profile surface is used).
9. Reasoning-effort semantics strategy:
   - reasoning-effort fields are explicit and typed:
     - `reasoning_effort_requested`
     - `reasoning_effort_observed`
     - `reasoning_effort_source_kind`
   - ambiguous single-field effort claims are invalid.
10. Hidden branching posture strategy:
   - prompt-only hidden branching may not be treated as equivalent to explicit ladder
     occupation;
   - branching that affects emitted posture must be reflected in typed run surfaces:
     - `branching_posture`
     - `branching_visibility_status`
     - `branch_event_refs`.
11. Narrative non-authority strategy:
   - summaries are descriptive-only and may not override typed occupation/authority
     fields.
12. Local-first and widening strategy:
   - this slice is limited to one bounded local reasoning run attempt;
   - `V42-G3` and `V42-G4` remain deferred.

## Required Deliverables

1. New typed reasoning-run bridge surface:
   - canonical `adeu_arc_reasoning_run_record@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic run-bridge entrypoints that:
   - consume one released puzzle-input bundle plus one selected puzzle entry;
   - execute one bounded reasoning-agent attempt;
   - emit typed in-band ladder refs for task/observation/hypothesis/action (and rollout
     when present) with stage-aware evidence refs and monotonic emission sequence;
   - fail closed on missing/malformed intermediate surfaces, identity drift, staged
     evidence gaps, or all-at-once compatible dump posture;
   - support blocked/deferred action-proposal posture without forcing committed rollout.
3. Top-level schema anchors for `adeu_arc_reasoning_run_record@1`:
   - `schema`
   - `reasoning_run_record_id`
   - `run_id`
   - `puzzle_input_bundle_id`
   - `selection_register_id`
   - `puzzle_input_id`
   - `puzzle_id`
   - `environment_ref`
   - `session_ref`
   - `competition_scope_ref`
   - `model_id`
   - `agent_profile_ref`
   - `run_config_ref`
   - `run_config_hash`
   - `prompt_profile_ref`
   - `reasoning_effort_requested`
   - `reasoning_effort_observed`
   - `reasoning_effort_source_kind`
   - `task_packet_ref`
   - `observation_frame_ref`
   - `hypothesis_frame_ref`
   - `action_proposal_ref`
   - `rollout_trace_ref`
   - `task_packet_emission_evidence_refs`
   - `observation_frame_emission_evidence_refs`
   - `hypothesis_frame_emission_evidence_refs`
   - `action_proposal_emission_evidence_refs`
   - `rollout_trace_emission_evidence_refs`
   - `emission_sequence_register`
   - `run_execution_status`
   - `run_terminal_posture`
   - `rollout_presence_posture`
   - `branching_posture`
   - `branching_visibility_status`
   - `branch_event_refs`
   - `settlement_posture_carry`
   - `run_summary`
   - `evidence_refs`
4. Deterministic laws that fail closed on at least:
   - any run record not bound to one released puzzle-input bundle and one selected puzzle
     entry;
   - any run record missing required in-band intermediate refs for task/observation/
     hypothesis/action;
   - any run record missing `action_proposal_ref` (including blocked/deferred outcomes);
   - any attempt that claims stage occupation while corresponding stage-aware emission
     evidence refs are missing;
   - any `emission_sequence_register` that is missing, non-monotonic, or inconsistent
     with stage-evidence ordering;
   - any artifact-compatible all-at-once dump posture where stage refs are present but
     staged emission evidence ordering is absent;
   - any `rollout_presence_posture` or `run_terminal_posture` that contradicts
     `rollout_trace_ref` presence/absence;
   - any run-lifecycle transition outside bounded `run_execution_status` enum progression;
   - any identity-chain mismatch across run/puzzle/environment/session/competition refs;
   - any run with missing/contradictory agent/config identity anchors;
   - any run posture that treats prompt-only hidden branching as equivalent to explicit
     typed ladder occupation;
   - any branching-affecting posture represented without typed branching visibility
     surfaces;
   - any deterministic replay claim that depends on fresh model re-execution rather than
     fixed emitted artifacts and fixed in-band evidence;
   - any summary content presented as authoritative over typed run surfaces.
5. Committed reference fixtures under `apps/api/fixtures/arc_agi/vnext_plus96/`:
   - one accepted single-attempt run record with explicit in-band ladder occupation;
   - one rejected run record with post-hoc reconstruction posture;
   - one rejected run record with missing intermediate observation/hypothesis/action
     occupancy;
   - one rejected run record with all required refs present but missing monotonic
     staged-emission evidence ordering;
   - one rejected run record with puzzle/identity-chain mismatch;
   - one rejected run record with hidden-branching laundering over typed surfaces;
   - one rejected run record with rollout-presence posture contradiction.
6. Python tests covering:
   - schema/model validation for run-record artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for accepted single-attempt run fixture;
   - rejection of post-hoc reconstruction, intermediate-surface omissions, all-at-once
     dump posture, identity/config-chain mismatch, hidden-branching laundering, and
     rollout-posture contradiction.

## Hard Constraints

- `vNext+96` may not reopen or redefine released `V41`, released `V42-A`..`V42-F`, or
  released `V42-G1` contracts.
- `vNext+96` may not widen into three-puzzle harness orchestration (`V42-G3`) or behavior
  evidence synthesis (`V42-G4`).
- `vNext+96` may not ship benchmark tournament orchestration execution, API/web operator
  routes, or generalized multi-agent/multi-benchmark orchestration.
- `vNext+96` must treat puzzle bundle and selection-register authority as typed required
  inputs; ambient prompt-only selection is invalid.
- `vNext+96` deterministic replay claims must be limited to fixed emitted artifacts plus
  fixed in-band evidence; deterministic fresh model re-execution claims are forbidden.
- `vNext+96` must preserve fail-closed posture for skipped/malformed intermediate
  surfaces and for missing/non-monotonic staged-emission evidence.
- `vNext+96` must emit `action_proposal_ref` even in blocked/deferred posture; this slice
  may not force committed rollout as a validity precondition.
- `vNext+96` may not treat narrative run summary fields as authoritative over typed run
  identity and occupation fields.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- run-bridge schema release, deterministic entrypoint wiring, fixture ladder, and
  anti-reconstruction fail-closed checks are one tightly coupled seam;
- splitting these across multiple PRs would create temporary contract drift for the same
  bounded `V42-G2` lane.
