# Draft Next Arc Options v24

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`, updated after
`vNext+92` closeout and released `V42-D` ARC local-eval baseline on `main`.

This draft moves from "bounded repo-grounded practical analysis is complete" to the next
family-selection question:

how should ADEU Studio use the released practical-analysis substrate to participate in an
external interactive benchmark, specifically ARC-AGI-3, without collapsing back into
opaque prompt-only agent behavior?

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
- `vNext+92` is the current baseline implementation state.
- `V42-A` is now closed on `main` at its intentionally bounded scope:
  - official local ARC toolkit adapter grounding;
  - canonical `adeu_arc_task_packet@1`;
  - explicit deontic mode/legal envelope boundary;
  - deterministic packet replay fixtures;
  - no observation/hypothesis/action/scorecard widening.
- `V42-B` is now closed on `main` at its intentionally bounded scope:
  - canonical `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1`;
  - first-class ontology inventory and denominator-bound decomposition coverage;
  - explicit direct-vs-derived observation typing and ambiguity carry-through;
  - explicit utility-pressure register and non-committing working-hypothesis posture;
  - fail-closed rejection of observation/hypothesis bleed and unsupported impossibility
    posture;
  - no action/rollout/scorecard/competition widening.
- `V42-C` is now closed on `main` at its intentionally bounded scope:
  - canonical `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1`;
  - explicit proposal status, decision-basis surfaces, utility posture, and
    ambiguity-preserving alternative-action register;
  - structured pre-action expectation surfaces with expectation hash identity;
  - deterministic rollout lineage with pre-step/post-step state refs;
  - fail-closed rejection of hidden tactical utility laundering, expectation-lineage
    omissions, post-hoc expectation rewrite, and retroactive necessity laundering;
  - no scorecard/replay/competition widening.
- `V42-D` is now closed on `main` at its intentionally bounded scope:
  - canonical `adeu_arc_local_eval_record@1` over released
    `V42-A`/`V42-B`/`V42-C` lineage;
  - explicit task-success versus control-plane-adherence separation with typed
    adherence decomposition;
  - explicit evaluation provenance anchors and per-model/run identity posture;
  - orthogonality fixture coverage across task outcome and control-plane adherence;
  - fail-closed rejection of authority leakage, leaderboard overclaim, and local
    trajectory necessity laundering;
  - no scorecard/replay/competition widening.
- The released practical-analysis substrate now includes:
  - canonical analysis request, settlement, observation, intended, alignment, and run
    manifest artifacts;
  - explicit frozen-world, settlement, observed, intended, alignment, and runner
    reasoning discipline;
  - deterministic replay over one bounded repo world;
  - review and intent-stress harness prompts that now exercise the same six-lane
    control posture over code review and doctrine review.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md` remains the authoritative closure record for the
  completed `V41` family.

## Gap

The missing layer is no longer repo-grounded practical reasoning over one internal code
world.

The missing layer is no longer first-contact adapter grounding.

`V42-A` established that baseline.

The missing layer now is scorecard/replay and competition-mode integration over the
released local evaluation baseline, specifically:

- consume the official ARC toolkit as the environment authority rather than replacing
  it;
- keep released decomposition/action lineage surfaces separate from scorecard authority
  and competition/deployment posture;
- preserve explicit local-vs-online authority boundaries so local evaluation does not
  silently mint scorecard authority;
- carry released local evaluation lineage into scorecard/replay seams without collapsing
  settlement/entitlement posture;
- widen into online scorecard and competition posture only after local benchmark/eval
  doctrine is already explicit and machine-checkable.

Today the repo still lacks a released way to:

- release a bounded scorecard/replay manifest family that is lineage-bound to released
  local-eval records;
- express competition-mode posture and online authority boundaries without laundering
  local evaluation success into challenge-readiness claims;
- bind scorecard/replay artifacts back to released local-eval evidence while preserving
  fail-closed control-plane-honesty posture;
- widen into scorecard/competition seams without collapsing explicit deontic and
  settlement discipline.

## Recommended Family

- Family name: `V42`
- Family theme: ADEU ARC-AGI-3 participation substrate
- Closed prior family:
  - `V41-A`
  - `V41-B`
  - `V41-C`
  - `V41-D`
  - `V41-E`
  - `V41-F`
- Recommended architecture reference:
  - `docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md`
- Recommended decomposition reference:
  - `docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md`
- Recommended next path:
  - `V42-E`
- Recommended next concrete arc:
  - `vNext+93`
- Default path selection:
  - select `V42-E` as the next default candidate

## Closed Earlier Paths

### `V41`

Solved:

- one explicit practical reasoning loop over a bounded repo world;
- explicit frozen-world, settlement, observed, intended, alignment, and runner
  separation;
- deterministic replay and fail-closed blocked posture over one internal code analysis
  workflow;
- prompt-facing harness docs that make the six-lane control surface reusable beyond the
  original implementation family.

`V41` is therefore a usable internal reasoning substrate.

It is not yet an external interactive benchmark adapter.

### `V42-A`

Solved:

- official local ARC toolkit adapter grounding with fail-closed authority posture;
- canonical `adeu_arc_task_packet@1` with deterministic full-packet identity;
- explicit mode posture, legal-action envelope, and legality normalization provenance;
- explicit deontic boundary constraints with policy-semantic smuggling rejection;
- rejection of synthetic prompt-authored packets presented as toolkit authority.

`V42-A` is complete on `main` at intentionally bounded scope.

### `V42-B`

Solved:

- deterministic ARC observation/hypothesis release over frozen `V42-A` packets;
- first-class ontology decomposition inventory and denominator-bound decomposition
  coverage;
- explicit direct-vs-derived observation typing, unresolved carry-through, and
  ambiguity register;
- explicit utility-pressure register and non-committing working-hypothesis posture;
- fail-closed rejection of observation/hypothesis bleed and unsupported impossibility
  posture.

`V42-B` is complete on `main` at intentionally bounded scope.

### `V42-C`

Solved:

- deterministic ARC action-proposal and rollout-trace release over frozen
  `V42-A`/`V42-B` artifacts;
- explicit deontic admissibility gate and non-forced blocked/deferred proposal posture;
- explicit proposal decision-basis and utility posture carry-through;
- structured expectation surface capture with hash identity and expectation/outcome
  comparison in rollout;
- deterministic pre-step/post-step lineage and settlement-posture carry-through;
- fail-closed rejection of hidden utility laundering, expectation rewrite, and
  retroactive necessity laundering.

`V42-C` is complete on `main` at intentionally bounded scope.

### `V42-D`

Solved:

- deterministic local-eval record release over frozen `V42-A`/`V42-B`/`V42-C` lineage;
- explicit task-success and control-plane-adherence separation with typed adherence
  decomposition;
- explicit evaluation provenance anchors and per-model/per-run identity posture;
- explicit orthogonality fixture coverage for task-outcome and adherence independence;
- fail-closed rejection of authority leakage and leaderboard overclaim from local-only
  evidence.

`V42-D` is complete on `main` at intentionally bounded scope.

## Recommended Next Family (`V42`)

`V42` should turn the released internal reasoning substrate into a local-first ARC
participation baseline.

The family should treat the official ARC toolkit as:

- authoritative for environment state and legal external interaction;
- not something ADEU tries to replace with repo-local imitation.

The family should treat ADEU as:

- the explicit reasoning control plane;
- the typed artifact and replay substrate;
- the place where hidden interpretation, action selection, and scorecard lineage
  become explicit.

The family should also treat model fit as empirical rather than assumed:

- stronger and weaker models may not inhabit the ADEU control plane equally well;
- local benchmarking should therefore evaluate both task success and control-plane
  adherence;
- no blanket model-agnostic uplift claim should be assumed by the family doctrine.

## Suggested `V42` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V42-A` | local toolkit adapter + task/session freeze | `adeu_arc_task_packet@1` plus bounded local adapter baseline | closed_on_main |
| `V42-B` | observed frame extraction + hypothesis register | `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1` | closed_on_main |
| `V42-C` | action proposal + rollout trace | `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1` | closed_on_main |
| `V42-D` | local benchmark runner / eval discipline | deterministic local ARC run/benchmark surface | closed_on_main |
| `V42-E` | online scorecard / replay integration | `adeu_arc_scorecard_manifest@1` and competition-mode adapter | deferred_to_later_family |

Additional possible widenings remain:

- API or web operator surfaces
  - `not_selected_yet`
- generalized multi-benchmark runtime
  - `not_selected_yet`
- multi-agent swarm orchestration inside ADEU
  - `not_selected_yet`

## Why This Family

- It is the narrowest lawful next step after the released `V41` practical-analysis
  baseline.
- It puts ADEU on a real external benchmark without immediately widening into product
  UI, generic multi-agent orchestration, or competition-mode deployment.
- It uses the official ARC toolkit as the environment authority, which reduces
  counterfeit environment semantics.
- It matches the practical lesson from the released six-lane loop:
  hidden interpretation is the failure mode, so the next external challenge path should
  make task/session freeze, observation, hypothesis, and action lineage explicit.
- It respects the official ARC recommendation to develop locally first before leaning
  on online scorecards or competition submission.

## Recommended Next Path (`V42-E`)

Implement the first explicit scorecard/replay and competition-mode widening over the
released `V42-D` local-eval baseline.

`V42-E` should introduce:

- one canonical bounded scorecard/replay manifest over released
  `V42-A`/`V42-B`/`V42-C`/`V42-D` lineage;
- explicit online-versus-local authority posture and deontic boundary carry-through;
- explicit replay-lineage binding from scorecard surfaces back to released local-eval
  evidence;
- fail-closed rejection of leaderboard/competition overclaim when scorecard authority
  posture is not explicitly satisfied.

## Path Boundary (`V42-E`)

`V42-E` should stay bounded to:

- scorecard/replay and competition-mode posture over released `V42-D` artifacts only;
- explicit online authority posture without reopening local-eval semantics;
- deterministic fixture/evidence posture for scorecard lineage boundaries;
- no product UI, API operator workbench, or generalized tournament orchestration seams.

It should not attempt:

- large search or multi-agent swarm infrastructure;
- full benchmark tournament orchestration beyond bounded scorecard/replay posture;
- web or API workbench surfaces;
- generic multi-benchmark abstraction;
- unrelated reopening of `V42-A` through `V42-D` semantics.

## Follow-On Path After `V42-E`

If `V42-E` lands cleanly, subsequent widening should be explicitly selected rather than
assumed by default.

Possible later candidates (not selected yet):

- API or web operator surfaces for ARC participation;
- large search or multi-agent swarm infrastructure;
- generalized multi-benchmark runtime;
- multi-agent orchestration or tournament-scale coordination;
- UI/workbench productization.

Before any post-`V42-E` widening is locked, the family decomposition should keep three
rules explicit:

- released scorecard/replay outputs may constrain but not mint claims outside explicit
  online authority posture;
- successful scorecard trajectories may not be laundered into universal necessity or
  blanket model-agnostic uplift claims;
- settlement/entitlement posture must remain explicit when widening from scorecard seams
  into product or orchestration seams.

The detailed family decomposition is not drafted yet.
The active decomposition reference for the current family is now:

- `docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md`

## Planning Boundary

- no reopening of the released `V41` repo-grounded practical-analysis contracts is
  authorized by this planning draft;
- no implicit claim that `V41` already solves external interactive benchmark
  participation is authorized by this planning draft;
- no competition-mode online submission, scorecard authority, or replay authority is
  authorized by this planning draft;
- no API or web workbench release for ARC participation is authorized by this planning
  draft;
- no generic multi-benchmark or multi-agent orchestration family is selected by this
  planning draft;
- no claim that ADEU should replace the official ARC toolkit as environment authority is
  authorized by this planning draft;
- no claim of leaderboard readiness or competitive challenge performance is authorized
  by this planning draft.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v23.md",
  "baseline_arc": "vNext+92",
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
  "active_family_status": "in_progress_with_v42a_v42b_v42c_v42d_closed_on_main",
  "closed_current_family_paths": [
    "V42-A",
    "V42-B",
    "V42-C",
    "V42-D"
  ],
  "default_next_arc_candidate": "V42-E",
  "default_next_concrete_arc_candidate": "vNext+93",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md",
  "family_decomposition_doc": "docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md",
  "challenge_reference": "ARC-AGI-3",
  "environment_authority": "official_arc_toolkit",
  "official_agent_wrapper_required": true,
  "local_first_required": true,
  "competition_mode_initially_deferred": true,
  "scorecard_authority_initially_deferred": true,
  "replay_authority_initially_deferred": true,
  "adapter_deontic_boundary_required": true,
  "v42a_task_packet_baseline_closed_on_main": true,
  "v42b_observation_hypothesis_baseline_closed_on_main": true,
  "v42c_action_rollout_baseline_closed_on_main": true,
  "v42d_local_eval_baseline_closed_on_main": true,
  "task_packet_artifact": "adeu_arc_task_packet@1",
  "observation_artifact": "adeu_arc_observation_frame@1",
  "hypothesis_artifact": "adeu_arc_hypothesis_frame@1",
  "action_proposal_artifact": "adeu_arc_action_proposal@1",
  "rollout_trace_artifact": "adeu_arc_rollout_trace@1",
  "local_eval_record_artifact": "adeu_arc_local_eval_record@1",
  "scorecard_manifest_artifact": "adeu_arc_scorecard_manifest@1",
  "observation_hypothesis_action_separation_required": true,
  "settlement_carry_required_before_hypothesis_action_widening": true,
  "odeu_decomposition_priority_before_heuristics": true,
  "control_plane_honesty_acceptance_required": true,
  "v42b_requires_static_odeu_decomposition_checklist_pass": true,
  "model_class_sensitivity_empirical_eval_required": true,
  "opaque_prompt_only_solving_rejected": true,
  "v41_practical_reasoning_substrate_reused": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md",
  "released_family_consumption_default": "stable_substrate_unless_explicitly_superseded",
  "next_family_decomposition_required_before_lock": true
}
```
