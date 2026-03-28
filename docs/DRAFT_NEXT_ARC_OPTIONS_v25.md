# Draft Next Arc Options v25

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v24.md`, updated after
`vNext+94` closeout to select a concrete post-`V42-F` path for local ARC-AGI-3 puzzle
testing with ADEU.

This draft moves from "post-submission widening is not selected yet" to an explicit
selection:

`V42-G` as a bounded local-testing lane with four subtasks (`G1`..`G4`) that make
ARC-AGI-3 puzzle ingestion, reasoning-run capture, and three-puzzle local evaluation
replayable through released ADEU artifacts.

`V42-G` is the first operationalization lane in this family: it does not primarily
widen the released artifact ladder; it consumes released `V42-A`..`V42-F` artifacts in a
bounded local-testing workflow.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior, schema release, or implementation by itself.

Interpretive doctrine for this planning surface:

- horizon-sensitive terms such as `bounded`, `complete`, `closed`, `deferred`, and
  `forbidden` should be read using
  `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`;
- planning-boundary lines below are scope guards and absence-of-authorization
  statements for this planning draft, not lock-equivalent permanent prohibitions by
  themselves;
- planning-vs-lock authority transfer should be read using
  `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`;
- future seam selection and widening posture should be read using
  `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`.

## Baseline

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` through `V41-F` are closed on `main`.
- `vNext+94` is the current baseline implementation state.
- `V42-A` through `V42-F` are closed on `main` at intentionally bounded scope:
  - `V42-A`: local toolkit adapter and canonical `adeu_arc_task_packet@1`;
  - `V42-B`: canonical observation and hypothesis artifacts;
  - `V42-C`: canonical action proposal and rollout trace artifacts;
  - `V42-D`: canonical local eval artifact and adherence/task orthogonality checks;
  - `V42-E`: canonical scorecard/replay authority posture artifact;
  - `V42-F`: canonical submission execution artifact with lifecycle separation and
    request/receipt/result identity-chain validation.
- The practical-analysis six-lane substrate from `V41` remains released and reusable.
- `V42-G` remains inside `V42` because it is ARC-participation-specific and consumes
  the released `V42-A`..`V42-F` stack without redefining those contracts.

## Gap

The missing layer is no longer schema-grounded local reasoning artifacts.

The missing layer now is practical local ARC-AGI-3 puzzle testing workflow over the
released `V42-A`..`V42-F` stack, specifically:

- get puzzle inputs into this repo in a deterministic, replayable, local-first way;
- run a reasoning agent through the ADEU scaffold so decomposition/observation/
  hypothesis/action traces are explicit;
- execute a bounded multi-puzzle local run (initially three puzzles) and retain full
  lineage and evidence;
- evaluate behavior quality and control-plane adherence from produced artifacts without
  requiring tournament/API/web widening.

Today the repo still lacks a released way to:

- standardize local ARC-AGI-3 puzzle fetch/ingest/freeze as a first-class ADEU lane;
- run one end-to-end local "reasoning agent attempt" flow that emits an auditable
  artifact ladder per puzzle using the current stack;
- aggregate a small local puzzle set run in one deterministic harness flow;
- ship a canonical behavior-mapping evidence bundle focused on how the agent reasons
  and where it fails under ADEU controls.
- verify that a reasoning run actually occupied the ADEU control plane during execution
  rather than being post-hoc reconstructed into artifact-compatible outputs.

## Recommended Family

- Family name: `V42`
- Family theme: ADEU ARC-AGI-3 participation substrate
- Recommended architecture reference:
  - `docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md`
- Recommended decomposition reference:
  - `docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V42-G` local ARC-AGI-3 testing lane over released `V42-A`..`V42-F` (workflow
    consumption lane, not primary artifact-ladder widening)
- Recommended next concrete arc:
  - `vNext+95` (`V42-G1`)
- Default path selection:
  - select `V42-G1` as the next default candidate;
  - instantiate `V42-G1` first, then advance `G2`..`G4` in order.

## Suggested `V42` Path Ladder

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V42-A` | local toolkit adapter + task/session freeze | `adeu_arc_task_packet@1` plus bounded local adapter baseline | closed_on_main |
| `V42-B` | observed frame extraction + hypothesis register | `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1` | closed_on_main |
| `V42-C` | action proposal + rollout trace | `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1` | closed_on_main |
| `V42-D` | local benchmark runner / eval discipline | deterministic local ARC run/benchmark surface | closed_on_main |
| `V42-E` | scorecard / replay posture | `adeu_arc_scorecard_manifest@1` | closed_on_main |
| `V42-F` | submission execution / bounded orchestration posture | `adeu_arc_submission_execution_record@1` | closed_on_main |
| `V42-G1` | local puzzle ingest and freeze | deterministic local ARC-AGI-3 puzzle input bundle + fixture ladder | planned |
| `V42-G2` | reasoning-agent ADEU run bridge | bounded local agent-run entrypoint over released `V42-A`..`V42-C` surfaces | planned |
| `V42-G3` | three-puzzle local run harness | deterministic `3`-puzzle execution/eval harness over released `V42-A`..`V42-F` | planned |
| `V42-G4` | behavior mapping and evidence bundle | canonical local behavior analysis/evidence package with fail-closed claim posture | planned |

## `V42-G` Four Subpath Subtasks

### `V42-G1` Local Puzzle Ingest and Freeze

Scope:

- authoritative puzzle source-kind binding and puzzle-identity provenance model must be
  explicit (copy, mirror, or external reference posture);
- deterministic selection register for the initial three-puzzle cohort must be declared
  before run outcomes are known;
- deterministic normalization/freeze into local fixtures with replay anchors and
  identity hashes per selected puzzle.

Non-goals:

- no solving quality claim;
- no tournament or online submission execution.

### `V42-G2` Reasoning-Agent Run Bridge

Scope:

- bounded local runner entrypoint that executes one reasoning agent attempt and emits
  released ADEU ladder artifacts (`V42-A`..`V42-C` minimum, plus downstream refs as
  applicable);
- explicit per-attempt identity, settlement carry-through, and fail-closed malformed
  output posture;
- artifact emission must be in-band execution discipline (not post-hoc reconstruction);
- skipped or malformed intermediate surfaces must fail closed;
- prompt-only hidden branching may not be treated as equivalent to explicit ladder
  occupation.

Non-goals:

- no multi-agent swarm lane;
- no product/API/operator surface widening.

### `V42-G3` Three-Puzzle Local Harness

Scope:

- deterministic orchestration of exactly three local puzzles through the released ADEU
  control plane;
- canonical local eval/scorecard/submission-posture handling remains bounded by released
  `V42-D`/`V42-E`/`V42-F` constraints;
- fixed selection-basis doctrine must be explicit (reference set or typed selection
  basis) and may not allow retrospective puzzle swap after outcomes are observed.

Non-goals:

- no benchmark tournament execution;
- no online-first authority claims.

### `V42-G4` Behavior Mapping and Evidence Bundle

Scope:

- canonical evidence outputs showing structure mapping, strategy evolution, and failure
  modes across the three-puzzle run;
- explicit non-authoritative narrative summaries constrained by typed artifacts;
- evidence synthesis only: this subpath may not mint new solver-rule authority or
  retroactive semantic reinterpretation absent from upstream typed artifacts.

Non-goals:

- no leaderboard-readiness or blanket competitiveness claims;
- no universal-necessity claims from bounded local outcomes.

## Why This Next Step

- It is the narrowest practical widening that directly answers "can we test ARC-AGI-3
  puzzles locally with ADEU right now?" without reopening closed `V42-A`..`V42-F`
  contracts.
- It keeps the repo in local-first mode while converting the existing artifact stack
  into a usable puzzle-testing workflow.
- It avoids premature tournament/API/web expansion while still generating actionable
  reasoning evidence for subsequent family choices.

## Planning Boundary

- no reopening of released `V41` or released `V42-A`..`V42-F` contracts is authorized
  by this planning draft;
- no benchmark tournament orchestration execution is authorized by this planning draft;
- no API or web operator product surface release is authorized by this planning draft;
- no generalized multi-benchmark or multi-agent orchestration family selection is
  authorized by this planning draft;
- no claim of leaderboard readiness, competition success, or model-agnostic universal
  uplift from bounded local three-puzzle evidence is authorized by this planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v24.md",
  "baseline_arc": "vNext+94",
  "closed_prior_family": "V41",
  "closed_prior_paths": [
    "V41-A",
    "V41-B",
    "V41-C",
    "V41-D",
    "V41-E",
    "V41-F"
  ],
  "active_family": "V42",
  "active_family_status": "in_progress_with_v42a_v42b_v42c_v42d_v42e_v42f_closed_on_main_and_v42g_planned",
  "closed_current_family_paths": [
    "V42-A",
    "V42-B",
    "V42-C",
    "V42-D",
    "V42-E",
    "V42-F"
  ],
  "planned_current_family_paths": [
    "V42-G1",
    "V42-G2",
    "V42-G3",
    "V42-G4"
  ],
  "default_next_arc_candidate": "V42-G1",
  "default_next_concrete_arc_candidate": "vNext+95",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "family_decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "challenge_reference": "ARC-AGI-3",
  "environment_authority": "official_arc_toolkit",
  "local_first_required": true,
  "v42a_task_packet_baseline_closed_on_main": true,
  "v42b_observation_hypothesis_baseline_closed_on_main": true,
  "v42c_action_rollout_baseline_closed_on_main": true,
  "v42d_local_eval_baseline_closed_on_main": true,
  "v42e_scorecard_baseline_closed_on_main": true,
  "v42f_submission_execution_baseline_closed_on_main": true,
  "v42g_lane_selected": true,
  "v42g_is_operationalization_lane": true,
  "v42g_consumes_released_v42a_to_v42f_without_redefinition": true,
  "v42g1_local_puzzle_ingest_freeze_planned": true,
  "v42g1_authoritative_puzzle_source_binding_required": true,
  "v42g1_predeclared_selection_register_required": true,
  "v42g2_reasoning_agent_run_bridge_planned": true,
  "v42g2_in_band_ladder_emission_required": true,
  "v42g2_post_hoc_artifact_reconstruction_rejected": true,
  "v42g3_three_puzzle_local_harness_planned": true,
  "v42g3_fixed_selection_basis_no_retrospective_swap_required": true,
  "v42g4_behavior_mapping_evidence_bundle_planned": true,
  "v42g4_evidence_synthesis_only_non_minting_required": true,
  "bounded_three_puzzle_initial_scope": true,
  "tournament_execution_deferred": true,
  "api_web_operator_surfaces_deferred": true,
  "generalized_multi_agent_orchestration_deferred": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md",
  "next_family_decomposition_required_before_lock": true
}
```
