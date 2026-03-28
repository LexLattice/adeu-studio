# Locked Continuation vNext+91

Status: `V42-C` implementation contract.

## V91 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v42c_arc_action_rollout_contract@1",
  "target_arc": "vNext+91",
  "target_path": "V42-C",
  "target_scope": "arc_action_proposal_and_rollout_trace_baseline_over_released_observation_hypothesis",
  "task_packet_schema": "adeu_arc_task_packet@1",
  "observation_frame_schema": "adeu_arc_observation_frame@1",
  "hypothesis_frame_schema": "adeu_arc_hypothesis_frame@1",
  "action_proposal_schema": "adeu_arc_action_proposal@1",
  "rollout_trace_schema": "adeu_arc_rollout_trace@1",
  "implementation_packages": [
    "adeu_arc_agi",
    "adeu_arc_solver"
  ],
  "authoritative_upstream_source": "V42-A_and_V42-B_released_artifacts",
  "local_first_required": true,
  "deontic_admissibility_gate_required": true,
  "proposal_decision_basis_required": true,
  "proposal_status_required": true,
  "utility_operational_surface_required": true,
  "structured_expectation_surface_required": true,
  "rollout_state_lineage_required": true,
  "expectation_outcome_lineage_required": true,
  "settlement_posture_carry_required": true,
  "post_hoc_expectation_rewrite_forbidden": true,
  "retroactive_necessity_laundering_forbidden": true,
  "alternative_action_register_required": true,
  "scorecard_and_competition_mode_deferred": true,
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md"
}
```

## Slice

- Arc label: `vNext+91`
- Family label: `V42-C`
- Scope label: ARC action proposal and rollout trace baseline over released observation/hypothesis

## Objective

Introduce the first tactical-action widening for ARC participation by releasing:

- one canonical `adeu_arc_action_proposal@1`; and
- one canonical `adeu_arc_rollout_trace@1`

over released `V42-A` task packets plus released `V42-B` observation/hypothesis artifacts,
while preserving explicit deontic admissibility, expectation-to-outcome lineage,
settlement posture carry-through, and control-plane honesty before any scorecard/replay
or competition-mode surface is released.

This slice establishes the first ADEU ARC action substrate for:

- deterministic action proposal over released hypothesis posture;
- explicit deontic admissibility checks tied to released legal-action envelopes;
- explicit action decision-basis and utility posture for why one legal action is chosen;
- explicit blocked/deferred non-commit posture when no action is yet entitled;
- structured expected-outcome surface captured before commitment;
- deterministic rollout step lineage and observed outcome capture;
- explicit pre-step/post-step state lineage per rollout step;
- explicit expectation-vs-outcome comparison without retroactive doctrine laundering;
- preserved ambiguity/claim posture across action and rollout artifacts;
- explicit alternative-action register carry-through under ambiguity;
- deterministic local fixture replay for accepted and rejected action/rollout cases.

This slice remains deliberately prior to:

- scorecard/replay manifest release;
- competition-mode online integration;
- benchmark tournament orchestration;
- API/web operator surfaces.

Its job is to prove that tactical action commitment can remain explicitly grounded in
released decomposition posture without widening into scorecard or deployment seams.

## Frozen Implementation Decisions

1. Active package strategy:
   - activate bounded `V42-C` surfaces in:
     - `packages/adeu_arc_agi` for authoritative schema ownership and canonical artifacts;
     - `packages/adeu_arc_solver` for bounded action/rollout derivation helpers;
   - no scorecard/replay or competition-mode helpers may be activated in this slice.
2. Upstream authority strategy:
   - `vNext+91` must consume released:
     - `adeu_arc_task_packet@1`,
     - `adeu_arc_observation_frame@1`,
     - `adeu_arc_hypothesis_frame@1`
     as the authoritative pre-action boundary;
   - it may not bypass upstream artifact authority with prompt-authored ambient state
     reinterpretation;
   - deontic legality remains sourced from released packet boundaries and may not be
     recomputed as hidden local doctrine.
3. Action-proposal strategy:
   - `adeu_arc_action_proposal@1` is authoritative for pre-action commitment in this slice;
   - each proposal must carry:
     - lineage refs to task packet, observation frame, and hypothesis frame;
     - `proposal_status` as exactly one of:
       - `admissible_candidate`
       - `blocked`
       - `deferred_pending_resolution`
     - proposal deontic admissibility posture;
     - explicit decision-basis surfaces:
       - `hypothesis_selection_basis`
       - `utility_pressure_basis`
       - `ambiguity_handling_basis`
       - `proposal_decision_basis`
     - selected hypothesis support refs;
     - explicit utility operational posture:
       - `proposal_utility_posture`
       - `alternative_action_register`
     - structured pre-action expectation surfaces:
       - `expected_state_delta`
       - `expected_hypothesis_effects`
       - `expected_falsification_conditions`
       - `expected_ambiguity_effects`
       - `expected_outcome_summary`
       - `expected_outcome_refs`
       - `expectation_surface_hash`.
4. Rollout-trace strategy:
   - `adeu_arc_rollout_trace@1` is authoritative for executed-step lineage in this slice;
   - rollout trace must carry:
     - deterministic step ordering;
     - proposal refs for each committed step;
     - `pre_step_state_ref` and `post_step_state_ref` per committed step;
     - observed outcome refs;
     - `expectation_surface_ref` and `expectation_surface_hash` that bind back to the
       pre-action proposal expectation surface without rewrite;
     - explicit expectation-vs-outcome comparison posture;
     - `rollout_stop_reason`;
     - `outcome_hypothesis_effects`.
5. Settlement-carry strategy:
   - ambiguity/claim posture from `V42-B` must remain explicit in action and rollout artifacts;
   - if `proposal_status` is `blocked` or `deferred_pending_resolution`, no action may be
     emitted as committed under an admissible-candidate posture;
   - selecting one action under live ambiguity must not erase known alternative admissible
     branches without explicit alternative-action register carry-through;
   - successful outcomes may not retroactively mint universal task-rule necessity.
6. Local-first and widening strategy:
   - `vNext+91` remains local/offline only;
   - scorecard/replay authority and competition mode remain deferred to later paths.
7. Path decomposition strategy:
   - `vNext+91` is the first concrete `V42-C` arc;
   - any widening into `V42-D` benchmark/eval surfaces remains available only for later
     concrete arcs outside this lock.

## Required Deliverables

1. New typed action/rollout surface:
   - extend bounded ARC helpers under `packages/adeu_arc_agi` and
     `packages/adeu_arc_solver` to materialize canonical action proposal and rollout
     trace artifacts over released `V42-A`/`V42-B` artifacts;
   - export schema helpers for authoritative and mirrored JSON-schema output;
   - keep scorecard/replay/competition surfaces out of scope.
2. Canonical artifacts:
   - `adeu_arc_action_proposal@1`
   - `adeu_arc_rollout_trace@1`
3. Deterministic entrypoints that:
   - consume one released task packet, one released observation frame, and one released
     hypothesis frame;
   - materialize one canonical action proposal;
   - materialize one canonical rollout trace;
   - fail closed when lineage, deontic admissibility, settlement-carry posture,
     decision-basis/utility posture, or expectation-outcome lineage is invalid.
4. Top-level schema anchors for `adeu_arc_action_proposal@1`:
   - `schema`
   - `action_proposal_id`
   - `task_packet_id`
   - `task_packet_ref`
   - `observation_frame_id`
   - `observation_frame_ref`
   - `hypothesis_frame_id`
   - `hypothesis_frame_ref`
   - `proposal_step_index`
   - `proposal_status`
   - `proposed_action_kind`
   - `proposed_action_payload`
   - `proposal_deontic_admissibility`
   - `proposal_decision_basis`
   - `hypothesis_selection_basis`
   - `utility_pressure_basis`
   - `ambiguity_handling_basis`
   - `proposal_utility_posture`
   - `supporting_hypothesis_refs`
   - `alternative_action_register`
   - `expected_state_delta`
   - `expected_hypothesis_effects`
   - `expected_falsification_conditions`
   - `expected_ambiguity_effects`
   - `expected_outcome_summary`
   - `expected_outcome_refs`
   - `expectation_surface_hash`
5. Top-level schema anchors for `adeu_arc_rollout_trace@1`:
   - `schema`
   - `rollout_trace_id`
   - `task_packet_id`
   - `task_packet_ref`
   - `rollout_steps`
   - `pre_step_state_refs`
   - `post_step_state_refs`
   - `terminal_rollout_status`
   - `rollout_stop_reason`
   - `outcome_hypothesis_effects`
   - `expectation_surface_ref`
   - `expectation_surface_hash`
   - `expectation_outcome_comparison`
   - `settlement_posture_carry`
6. Deterministic laws that fail closed on at least:
   - any action proposal not lineage-bound to one released task packet/observation/hypothesis set;
   - any action proposal missing `proposal_status` or carrying status outside released enum;
   - any proposed action outside released legal-action envelope;
   - any proposal emitted as committed action while `proposal_status` is `blocked` or
     `deferred_pending_resolution`;
   - any action proposal missing explicit decision-basis or utility posture surfaces while
     claiming hypothesis-guided tactical selection;
   - any action proposal missing structured expectation surfaces;
   - any ambiguity-bearing proposal missing alternative-action register carry-through;
   - any rollout step lacking proposal or observed-outcome refs;
   - any rollout step lacking pre-step/post-step state lineage refs;
   - any rollout trace with non-deterministic or non-monotonic step ordering;
   - any expectation-vs-outcome comparison omitted while claiming rollout completion;
   - any rollout trace whose expectation surface does not resolve byte-identically to the
     pre-action proposal expectation surface (`expectation_surface_hash` mismatch);
   - any rollout artifact that rewrites expected outcome structure post-hoc after observed
     outcome capture;
   - any successful rollout that retroactively emits universal necessity claims without
     explicit supporting entitlement posture;
   - any hidden utility laundering where tactical choice is justified only by prose without
     machine-checkable decision-basis and utility fields;
   - any attempt to mint scorecard/replay/competition authority inside `V42-C` artifacts.
7. Committed reference fixtures:
   - one accepted fixture ladder under `apps/api/fixtures/arc_agi/vnext_plus91/` covering:
     - one deterministic action proposal + rollout trace over released `V42-B` artifacts;
     - one rejected proposal outside legal-action envelope;
     - one rejected proposal with hidden utility/tactical commitment laundering
       (missing decision-basis/utility posture under ambiguity);
     - one rejected rollout trace with expectation-lineage omission;
     - one rejected rollout trace with post-hoc expectation surface rewrite;
     - one rejected rollout trace with retroactive necessity laundering posture.
   - accepted fixtures must prove:
     - deterministic replay;
     - explicit deontic admissibility carry-through;
     - explicit proposal decision-basis and utility posture carry-through;
     - explicit expectation-vs-outcome carry-through;
     - byte-stable expectation-surface identity from proposal into rollout trace;
     - explicit settlement posture carry-through;
     - no scorecard/replay leakage.
8. Python tests covering:
   - schema/model validation for action proposal and rollout trace artifacts;
   - authoritative/mirrored schema export parity;
   - deterministic replay from accepted fixture ladder;
   - rejection of deontically inadmissible action proposals;
   - rejection of hidden utility/tactical commitment laundering;
   - rejection of expectation-lineage omissions;
   - rejection of post-hoc expectation surface rewrite;
   - rejection of retroactive necessity laundering;
   - rejection of scorecard/replay leakage in `V42-C`.

## Hard Constraints

- `vNext+91` may not reopen or redefine released `V41`, `V42-A`, or `V42-B` contracts.
- `vNext+91` may not ship:
  - `adeu_arc_scorecard_manifest@1`,
  - replay authority artifacts,
  - competition-mode online submission,
  - benchmark tournament orchestration,
  - API/web operator routes,
  - leaderboard-readiness claims.
- `vNext+91` may not treat prose-only narrative as sufficient for action admissibility
  or expectation-outcome lineage validation.
- `vNext+91` may not force committed-action posture when honest status is `blocked` or
  `deferred_pending_resolution`.
- `vNext+91` may not rewrite proposal expectation surfaces after rollout outcomes are
  observed.
- `vNext+91` may not hide tactical choice basis or utility posture behind summary-only
  prose when claiming hypothesis-guided action selection.
- `vNext+91` may not mint post-hoc necessity claims from rollout success without explicit
  entitlement.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- action-proposal and rollout-trace release is one bounded tactical seam;
- splitting schema, derivation, fixtures, and fail-closed laws would create artificial
  staging inside the same `V42-C` boundary without reducing semantic risk.
