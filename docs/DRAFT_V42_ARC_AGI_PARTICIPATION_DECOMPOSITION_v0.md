# Draft V42 ARC-AGI Participation Decomposition v0

Status: working decomposition draft after `vNext+90` closeout on `main`, where
`V42-A` and `V42-B` are now released at bounded scope.

This document is an intermediate planning artifact between:

- the released `V41` practical-analysis baseline;
- the high-level ARC participation architecture in
  `docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md`; and
- the first `V42` lock bundle.

This is not a lock doc. It does not authorize runtime behavior, schema release, or
implementation by itself.

## Purpose

- compile ADEU's ARC-AGI-3 participation goal into bounded, family-sized slices;
- prevent a direct jump from "ADEU has a six-lane practical reasoning substrate" to
  "ADEU ships a full ARC solver stack in one family start";
- keep the official ARC toolkit as environment authority while making ADEU's internal
  reasoning and replay posture explicit;
- make deontic adapter boundaries, settlement carry-through, and model-sensitivity
  evaluation explicit before the first lock is drafted.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v24.md`
- `docs/DRAFT_PRACTICAL_HARNESS_FLOW_v0.md`
- `docs/DRAFT_PRACTICAL_REASONING_SIX_LANE_LOOP_v0.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`
- `docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md`
- `docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md`

## Decomposition Thesis

`V41` solved an internal practical reasoning loop over one bounded repo world:

```text
frozen world
    -> settlement / entitlement
    -> observed facts
    -> intended interpretation
    -> alignment findings
    -> habitual run summary
```

`V42` does not replace that loop.

It rehosts that loop over an external interactive benchmark where the official ARC
toolkit owns environment truth and ADEU owns the internal reasoning and evidence
control plane.

The safe first move is therefore not:

- competition-mode deployment;
- scorecard lineage release;
- generalized ARC solver search;
- multi-agent orchestration;
- or leaderboard-readiness claims.

The safe first move is:

- freeze one official local ARC game/task/session boundary into a canonical task
  packet;
- make ARC-side mode and action legality first-class deontic surfaces;
- prove ADEU can wrap the official local adapter without inventing environment
  semantics.

After `vNext+90`, the first two bounded moves are now complete:

- `V42-A`: official local adapter + frozen task packet baseline;
- `V42-B`: explicit ontology/observation/hypothesis decomposition baseline.

The next move should keep the same doctrine order:

- first semantic anatomy and decomposition quality (`O/E/D/U`) over frozen ARC packets;
- then tactical reasoning machinery over that explicit decomposition.

In short:

```text
first semantic anatomy, then tactical intelligence
```

## Baseline Agreement

- `V39-A` through `V39-E` are closed on `main`.
- `V40-A` through `V40-F` are closed on `main`.
- `V41-A` through `V41-F` are closed on `main`.
- `V42-A` is closed on `main`.
- `V42-B` is closed on `main`.
- `vNext+90` is the current baseline implementation state.
- The next safe step is not to reopen `V41` or to widen straight into ARC observation,
  hypothesis, action, rollout, or scorecard semantics without first locking the
  environment-adapter boundary.
- The official ARC toolkit should remain the environment authority in this family.
- Local/offline mode should remain the first execution horizon in this family.
- Model fit should be treated as empirical rather than assumed: later local evaluation
  should measure both benchmark performance and whether the model actually inhabits the
  explicit ADEU control plane.

## Machine-Checkable Decomposition Baseline

```json
{
  "schema": "v42_arc_agi_participation_decomposition@1",
  "source_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "baseline_arc": "vNext+90",
  "closed_prior_family": "V41",
  "closed_prior_paths": [
    "V41-A",
    "V41-B",
    "V41-C",
    "V41-D",
    "V41-E",
    "V41-F"
  ],
  "next_path_family": "V42",
  "closed_current_family_paths": [
    "V42-A",
    "V42-B"
  ],
  "default_next_arc_candidate": "V42-C",
  "default_next_concrete_arc_candidate": "vNext+91",
  "v42_path_count": 5,
  "planned_family_packages": [
    "packages/adeu_arc_agi",
    "packages/adeu_arc_solver"
  ],
  "first_slice_active_packages": [
    "packages/adeu_arc_agi"
  ],
  "official_environment_authority": "official_arc_toolkit",
  "official_local_adapter_required": true,
  "local_first_required": true,
  "competition_mode_initially_deferred": true,
  "scorecard_authority_initially_deferred": true,
  "replay_authority_initially_deferred": true,
  "task_packet_artifact": "adeu_arc_task_packet@1",
  "v42a_static_semantic_anatomy_priority_required": true,
  "deontic_boundary_surface_required": true,
  "control_plane_honesty_acceptance_required": true,
  "v42b_static_decomposition_gate_closed_on_main": true,
  "v42c_action_rollout_gate_required": true,
  "settlement_carry_required_before_hypothesis_action_widening": true,
  "model_class_sensitivity_empirical_eval_required": true,
  "opaque_prompt_only_solving_rejected": true,
  "forbidden_first_lock_widenings": [
    "competition_mode_online_submission",
    "scorecard_or_replay_authority_release",
    "full_solver_search_stack_release",
    "api_or_web_operator_surface_release",
    "leaderboard_or_competitiveness_claims",
    "environment_semantics_redefinition"
  ]
}
```

## Family Scale Rules

To stay aligned with prior ADEU implementation families, `V42` should obey these
decomposition rules:

- the first slice introduces one practical seam, not a whole ARC solver ladder;
- official ARC environment truth remains external authority and may not be silently
  copied into repo-local substitutes;
- mode-policy and action-legality boundaries must be typed `D` surfaces, not prose-only
  context;
- no hypothesis or action-proposal slice is allowed to drop settlement / entitlement
  posture once that seam is introduced;
- no family slice should assume model-agnostic uplift from the ADEU harness;
- no slice should mix local adapter baseline, scorecard authority, competition-mode
  policy, and UI/workbench release in one lock.
- ARC decomposition should be judged statically before tactical heuristics are widened:
  - `O`: ontology units and boundaries;
  - `E`: direct-vs-derived observation and explicit epistemic posture;
  - `D`: legal action/mode admissibility boundaries;
  - `U`: explicit utility/pressure surfaces without hidden certainty minting.

## Package Activation Timing

- `packages/adeu_arc_agi` is the natural home for the first canonical ARC task/session
  packet and its local adapter-boundary policy.
- `packages/adeu_arc_solver` is now active at bounded scope for `V42-B`
  observation/hypothesis derivation helpers;
- further widening inside `adeu_arc_solver` into action/rollout policy logic remains
  deferred to `V42-C`.
- `apps/api` and `apps/web` integration remain deferred until the family proves the
  lower-level ARC adapter and task-packet contract first.

## Concrete Arc Granularity

`V42` path labels are not assumed to map one-to-one onto concrete `vNext+` arcs.

The current recommended concrete split is:

- `vNext+89` (closed on `main`)
  - first concrete `V42-A` arc:
    local ARC toolkit adapter and canonical `adeu_arc_task_packet@1` baseline,
    including task/session freeze, local mode posture, legal-action envelope, and
    adapter-boundary policy
- `vNext+90` (closed on `main`)
  - first concrete `V42-B` arc:
    explicit observed ARC frame extraction plus ontology inventory,
    denominator-bound decomposition coverage, hypothesis register, ambiguity /
    claim-posture carry-through, and utility-pressure posture
- later `V42-C`
  - first action and rollout widening:
    explicit action proposal, admissibility posture, and rollout trace
- later `V42-D`
  - local benchmark runner / evaluation discipline:
    deterministic local benchmark surface that measures both task success and
    control-plane adherence
- later `V42-E`
  - online scorecard/replay integration:
    scorecard lineage and competition-mode adapter if the family still selects that
    widening

## Recommended `V42` Slice Ladder

| Path | Theme | Primary output | Baseline role |
|---|---|---|---|
| `V42-A` | local adapter + task/session freeze | `adeu_arc_task_packet@1` and adapter-boundary contract | required |
| `V42-B` | observed frame extraction + hypothesis state | `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1` | closed_on_main |
| `V42-C` | action proposal + rollout trace | `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1` | deferred_to_later_family |
| `V42-D` | local benchmark runner / eval discipline | deterministic local ARC benchmark surface | deferred_to_later_family |
| `V42-E` | scorecard / competition-mode integration | `adeu_arc_scorecard_manifest@1` and online adapter | not_selected_yet |

## Path `V42-A`: Local Adapter and Task/Session Freeze (Closed on Main)

Lock class: `L1`

Goal:

- establish one canonical task/session packet and one lawful local adapter boundary for
  ARC participation before any solver-scale widening.

Scope:

- canonical `adeu_arc_task_packet@1`;
- official local ARC toolkit adapter baseline;
- explicit mode posture and legal-action envelope;
- deterministic initial state capture and hash binding;
- exact local fixture/reference replay;
- no observation, hypothesis, action, rollout, or scorecard artifact release yet.

Out of scope:

- competition-mode submission;
- scorecard or replay authority;
- observation-frame extraction;
- hypothesis or action-proposal artifacts;
- online benchmarking;
- API or web workbench routes;
- solver competitiveness claims.

Acceptance:

- one accepted task/session packet fixture replays deterministically;
- the adapter contract rejects non-local or non-authoritative environment posture;
- legal-action / mode-policy surfaces are explicit and machine-readable;
- no hidden widening into solver or scorecard semantics is shipped in the slice.

Static decomposition doctrine carried forward from `V42-A` into `V42-B`:

- no hidden solver assumptions inside ontology or boundary-policy surfaces;
- no blending of observed facts and inferred hypotheses inside one lane;
- no post-hoc prose compliance accepted when control-plane semantics were not explicit
  at decision time.

`V42-B` closeout confirms this doctrine is now released at bounded scope.

## Next Path Gate (`V42-C`)

`V42-C` should not be selected as implementation-ready unless the following
action/rollout checklist remains explicit and passed:

- admissibility checklist:
  - every action proposal is explicitly deontic-admissible under released mode/legal
    boundaries;
  - no action legality is minted by model inference.
- expectation lineage checklist:
  - each action proposal binds to supporting hypothesis refs and expected outcomes;
  - rollout outcomes preserve expectation-to-outcome comparison without laundering.
- settlement posture checklist:
  - ambiguity/claim posture from `V42-B` survives into action/rollout artifacts;
  - successful rollout steps do not mint second-order necessity claims by default.
- bounded-widening checklist:
  - no scorecard/replay/competition authority is released in `V42-C`;
  - no benchmark tournament orchestration is smuggled into action/rollout surfaces.
- control-plane honesty checklist:
  - opaque solving plus post-hoc paraphrase is rejected as ADEU adherence.

## Bottom Line

`V42-A` and `V42-B` were intentionally bounded and are now closed on `main`.

The next family step is successful only if tactical action commitment remains explicitly
grounded in released ontology/observation/hypothesis posture before benchmark or
scorecard widening.

Any larger claim belongs to later `V42` selection, not to the family start.
