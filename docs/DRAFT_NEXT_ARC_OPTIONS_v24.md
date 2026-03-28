# Draft Next Arc Options v24

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`, updated after the
released `V41` practical-analysis family closeout and the addition of intent-doctrine
hygiene notes on `main`.

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
- `vNext+88` is the current baseline implementation state.
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

The missing layer is a governed external-benchmark adapter that can:

- consume the official ARC toolkit as the environment authority rather than replacing
  it;
- freeze interactive ARC game/task/session state into typed ADEU artifacts;
- carry mode restrictions, legal-action envelope, and adapter-boundary policy as
  first-class admissibility surfaces rather than as prose-only context;
- keep observation, hypothesis, action proposal, and rollout lineage explicit;
- use ADEU's reasoning control plane internally without treating hidden prompt
  branching as sufficient;
- develop locally first and widen to online/competition mode later under explicit
  policy.

Today the repo still lacks a released way to:

- map ADEU's practical six-lane loop onto one ARC-AGI-3 game/session lifecycle;
- carry official ARC mode constraints such as local-vs-online and competition-mode
  restrictions into typed ADEU contracts;
- carry ARC-side deontic boundaries as explicit legal/illegal adapter-envelope
  surfaces instead of as metadata-only fields;
- benchmark ADEU-guided ARC runs locally with typed replay/evidence rather than
  free-form experiment logs;
- measure whether a model is actually inhabiting the explicit control plane rather than
  merely paraphrasing it while solving opaquely;
- bind ARC scorecard/replay lineage back to ADEU-side artifacts once online widening is
  selected later.

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
  - `V42-A`
- Recommended next concrete arc:
  - `vNext+89`
- Default path selection:
  - select `V42-A` as the next default candidate

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
| `V42-A` | local toolkit adapter + task/session freeze | `adeu_arc_task_packet@1` plus bounded local adapter baseline | default first slice |
| `V42-B` | observed frame extraction + hypothesis register | `adeu_arc_observation_frame@1` and `adeu_arc_hypothesis_frame@1` | deferred_to_later_family |
| `V42-C` | action proposal + rollout trace | `adeu_arc_action_proposal@1` and `adeu_arc_rollout_trace@1` | deferred_to_later_family |
| `V42-D` | local benchmark runner / eval discipline | deterministic local ARC run/benchmark surface | deferred_to_later_family |
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

## Recommended Next Path (`V42-A`)

Implement the local ARC toolkit adapter and frozen task/session packet baseline.

`V42-A` should introduce:

- one canonical `adeu_arc_task_packet@1` artifact over one bounded ARC game/task/session
  state;
- one bounded local adapter surface that talks to the official ARC toolkit rather than
  to repo-local fake environments;
- one explicit adapter-boundary policy or equivalent legal-action / mode-policy surface
  carried by the task packet or validated adapter contract;
- explicit capture of:
  - mode posture such as local/offline;
  - game/task identity;
  - session identity;
  - action-budget or mode constraints visible at the adapter boundary;
  - legal external interaction envelope as a binary admissibility surface, not only as
    descriptive metadata;
- no competition-mode scorecard or replay authority yet;
- no claim of solver competitiveness by the first slice alone.

## First-Slice Boundary (`V42-A`)

`V42-A` should stay bounded to:

- local/offline ARC toolkit integration only;
- frozen task/session packet capture only;
- deontic adapter-boundary capture only;
- exact toolkit-adapter lineage only;
- deterministic fixtures or local reference cases only;
- one minimal bounded action-loop proof surface only if needed to validate the adapter
  contract;
- authoritative and mirrored schema export parity if a new artifact family lands.

It should not attempt:

- competition-mode online submission;
- scorecard or replay manifest release;
- large search or multi-agent swarm infrastructure;
- full observation, hypothesis, or action-proposal family release;
- web or API workbench surfaces;
- generic multi-benchmark abstraction;
- leaderboard or challenge-readiness claims;
- direct use of observation as hidden minted intent rather than explicit hypothesis
  posture.

## Follow-On Path After `V42-A`

If `V42-A` lands cleanly, the next default path should likely be `V42-B`.

That would be the first slice that turns raw ARC game/task state into explicit observed
facts and live competing hypotheses rather than leaving interpretation inside the
adapter.

Before `V42-B` or `V42-C` is locked, the family decomposition should make three rules
explicit:

- hypothesis and action-proposal artifacts must carry settlement-style claim posture and
  unresolved ambiguity state rather than only raw candidate content;
- successful local rollout may not silently mint second-order necessity claims about the
  task rule;
- local evaluation should measure both benchmark success and whether the model actually
  uses the explicit ADEU control plane.

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
  "baseline_arc": "vNext+88",
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
  "active_family_status": "selected_not_started",
  "closed_current_family_paths": [],
  "default_next_arc_candidate": "V42-A",
  "default_next_concrete_arc_candidate": "vNext+89",
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
  "task_packet_artifact": "adeu_arc_task_packet@1",
  "observation_artifact": "adeu_arc_observation_frame@1",
  "hypothesis_artifact": "adeu_arc_hypothesis_frame@1",
  "action_proposal_artifact": "adeu_arc_action_proposal@1",
  "rollout_trace_artifact": "adeu_arc_rollout_trace@1",
  "scorecard_manifest_artifact": "adeu_arc_scorecard_manifest@1",
  "observation_hypothesis_action_separation_required": true,
  "settlement_carry_required_before_hypothesis_action_widening": true,
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
