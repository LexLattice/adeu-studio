# Draft Next Arc Options v26

Status: planning draft after `docs/DRAFT_NEXT_ARC_OPTIONS_v25.md`, updated after the
contest-participation module seed was clarified beyond the Kaggle-only framing.

This draft moves from "post-`V42` family/path selection is not selected yet" to an
explicit candidate selection:

how should ADEU Studio generalize from the released ARC-AGI-3 participation stack into
a broader external governed contest participation family without widening prematurely
into autonomous contest execution?

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
- `vNext+98` is the current baseline implementation state.
- `V42-A` through `V42-G4` are closed on `main` at intentionally bounded scope:
  - `V42-A`: local toolkit adapter and canonical `adeu_arc_task_packet@1`;
  - `V42-B`: canonical observation and hypothesis artifacts;
  - `V42-C`: canonical action proposal and rollout trace artifacts;
  - `V42-D`: canonical local eval artifact and adherence/task orthogonality checks;
  - `V42-E`: canonical scorecard/replay authority posture artifact;
  - `V42-F`: canonical submission execution artifact with lifecycle separation and
    request/receipt/result identity-chain validation;
  - `V42-G1`: canonical local puzzle ingest/freeze surface and deterministic three-puzzle
    selection register posture;
  - `V42-G2`: canonical reasoning-agent run bridge surface with stage-aware in-band
    ladder evidence posture;
  - `V42-G3`: canonical three-puzzle local harness surface with deterministic selection
    order, exact-entry occupancy, and per-puzzle downstream/sequence evidence posture;
  - `V42-G4`: canonical behavior mapping/evidence bundle surface with support-bound
    cross-puzzle synthesis and fail-closed claim/authority posture.
- `V42` should now be read as a released contest-domain specialization:
  - one bounded external challenge family (`ARC-AGI-3`);
  - one authoritative external environment (`official_arc_toolkit`);
  - one local-first ADEU reasoning/evidence control plane over that challenge.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v25.md` is the authoritative planning record for the
  state where post-`V42` next-family selection remained unselected.

## Gap

The missing layer is no longer inside `V42`.

The missing layer is now a general contest-participation family that can:

- treat external contests as bounded governed worlds rather than ad hoc challenge pages;
- separate host adapters from general contest doctrine;
- make contest ontology, law, evaluation, resource, and timeline structure explicit;
- identify where reasoning AI is actually useful, marginal, or irrelevant in a contest;
- support later lawful strategy and bounded execution lanes without pretending that those
  lanes are safe to release first.

Today the repo still lacks a released way to:

- compile one non-ARC contest host into typed contest-world artifacts;
- normalize contest law and evaluation surfaces with fail-closed ambiguity posture;
- classify contests into reusable archetypes while separating archetype from leverage map;
- promote from contest-world compilation into tactical participation only through explicit
  typed gates.

## Recommended Family

- Family name: `V43`
- Family theme: ADEU external governed contest participation substrate
- Closed prior family:
  - `V42-A`
  - `V42-B`
  - `V42-C`
  - `V42-D`
  - `V42-E`
  - `V42-F`
  - `V42-G1`
  - `V42-G2`
  - `V42-G3`
  - `V42-G4`
- Recommended architecture reference:
  - `docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md`
- Supporting seed input:
  - `docs/DRAFT_KAGGLE_META_MODULE_SPEC_v0`
- Recommended decomposition reference:
  - required before the first `V43` lock (`not_selected_yet`)
- Recommended next path:
  - `V43-A`
- Recommended next concrete arc:
  - `vNext+99`
- Default path selection:
  - select `V43-A` as the next default candidate

## Closed Earlier Family (`V42`)

`V42` solved a bounded contest-domain specialization rather than a general
contest-participation doctrine.

It proved that ADEU can:

- treat one external challenge environment as authoritative;
- keep ADEU's internal reasoning and evidence control plane typed and replayable;
- preserve fail-closed local-first posture over task packets, observation, hypothesis,
  action, rollout, eval, scorecard, submission, harness, and behavior-evidence layers.

`V42` did not yet release a general host-agnostic contest-world compilation family.

That generalization is the next planning move.

## Recommended Next Family (`V43`)

`V43` should generalize from one released contest specialization to a broader doctrine:

- external contest as bounded governed world;
- host adapter as environment-specific normalization layer;
- contest-world compilation before tactical participation machinery;
- staged realization of the seed's first safe family shape across:
  - `V43-A`: host truth and packet kernel;
  - `V43-B`: rule/eval/resource/timeline compilation;
  - `V43-C`: archetype and leverage mapping;
- explicit distinction between:
  - host adapter,
  - contest archetype,
  - contest leverage map,
  - bounded contest instance,
  - domain specialization.

The family should treat Kaggle as:

- the first broad host adapter candidate;
- not the family name;
- not the only future host.

The family should treat released `V42` as:

- prior proof of shape for one contest-domain specialization;
- not something to reopen or redefine.

## Suggested `V43` Path Ladder

The current recommended path ladder is:

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V43-A` | host adapter + contest packet normalization | candidate `adeu_contest_packet@1` over one initial host adapter | planned |
| `V43-B` | rule/eval/resource/timeline compilation | candidate `adeu_contest_rule_surface@1`, `adeu_contest_eval_surface@1`, `adeu_contest_resource_timeline_surface@1`, and `adeu_contest_ambiguity_register@1` | planned |
| `V43-C` | archetype classification + leverage mapping | candidate `adeu_contest_archetype@1` and `adeu_contest_leverage_map@1` | planned |
| `V43-D` | lawful strategy catalog | candidate `adeu_contest_strategy_catalog@1` | planned |
| `V43-E` | strategy selection + stop-gate posture | candidate `adeu_contest_strategy_selection_report@1` | planned |
| `V43-F` | bounded run evidence + postmortem | candidate `adeu_contest_run_evidence@1` and `adeu_contest_postmortem_lane_report@1` | planned |

These output names are planning-level candidate names, not lock-level schema authority.

`V43-A` through `V43-C` should be read together as the staged realization of the
contest-participation seed's first safe family shape.

That is:

- `V43-A` intentionally narrows the first move to host-truth and packet normalization;
- `V43-B` then compiles rule/eval/resource/timeline surfaces over that packet kernel;
- `V43-C` then adds archetype and leverage mapping over the released contest-world
  surfaces.

So the `A -> B -> C` staging is an intentional lower-risk subdivision, not a deviation
from the seed's contest-world-compilation-first doctrine.

## Recommended Next Path (`V43-A`)

Implement the bounded contest host-adapter and contest-packet lane first.

`V43-A` should introduce:

- one initial broad host adapter candidate surface:
  - Kaggle-first, without making Kaggle the family name;
- one canonical normalized contest packet candidate artifact;
- explicit observed-vs-derived source separation inside the packet;
- explicit host authority anchors for:
  - contest identity,
  - source URLs/materials,
  - organizer/host ownership posture,
  - extraction-confidence and missing-facts posture;
- explicit planning-level minimum identity contract for the packet covering at least:
  - host adapter identity;
  - bounded contest instance identity;
  - source-material set identity;
  - extraction run or snapshot identity;
  - observed-versus-derived field posture;
  - missing-facts or unresolved-slot posture;
- deterministic fixture coverage for one or more bounded reference contests from the
  first selected host adapter;
- no tactical execution widening beyond bounded source normalization and packet release.

## Why This Path

- It is the narrowest safe consumer of the new contest-participation seed.
- It establishes the host-truth boundary before strategy or execution surfaces are added.
- It prevents the family from collapsing into "contest executor" too early.
- It creates the minimal reusable substrate needed for later:
  - rule/eval/resource compilation;
  - archetype classification;
  - leverage mapping.
- It generalizes beyond `V42` without pretending that the released ARC-specific packet
  family is already a general contest packet family.

## First-Slice Boundary (`V43-A`)

`V43-A` should stay bounded to:

- one initial host adapter candidate;
- contest source ingestion and normalization only;
- canonical contest packet emission only;
- explicit observed-vs-derived content separation;
- explicit missing-facts and extraction-confidence posture;
- deterministic local fixtures and replay over bounded reference contests.

It should not attempt:

- rule adjudication beyond normalized extraction;
- legality resolution from ambiguous materials;
- contest archetype classification;
- leverage mapping;
- strategy generation or portfolio selection;
- bounded run evidence or postmortem execution lanes;
- notebook/submission automation;
- unrestricted browser/UI behavior;
- generalized multi-host orchestration.

## Follow-On Paths Inside `V43`

### `V43-B`

Contest-world law and evaluation compilation lane:

- candidate `adeu_contest_rule_surface@1`;
- candidate `adeu_contest_eval_surface@1`;
- candidate `adeu_contest_resource_timeline_surface@1`;
- candidate `adeu_contest_ambiguity_register@1`;
- fail-closed ambiguity posture for unresolved legality/evaluation questions.

### `V43-C`

Contest classification and leverage lane:

- candidate `adeu_contest_archetype@1`;
- candidate `adeu_contest_leverage_map@1`;
- explicit non-equivalence between "what kind of contest world is this?" and "where is
  reasoning AI useful here?".

This non-equivalence should be treated as a named family invariant, not merely as a
helpful implementation note.

### `V43-D`

Lawful strategy catalog lane:

- candidate branch families;
- legality/admissibility posture;
- epistemic risk posture;
- explicit bounded utility framing.

### `V43-E`

Strategy selection and promotion-law lane:

- explicit selection posture and rationale;
- explicit stop gates and escalation conditions;
- no self-authorizing jump into broad execution.

### `V43-F`

Bounded execution evidence and postmortem lane:

- candidate run evidence artifacts;
- lane-aware failure taxonomy;
- transferable findings versus contest-specific findings.

This lane remains intentionally later and higher-risk than `V43-A` through `V43-C`.

## Candidate Package Ownership

The first planning pass should assume one primary family package:

- `packages/adeu_contest`

The first slice should assume:

- `packages/adeu_contest` is the only active implementation package for `V43-A`.

Later tactical lanes may widen package ownership if the family actually reaches strategy
or execution-support surfaces.

## Governing References

The higher-order concept notes for this family direction are:

- `docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md`
- `docs/DRAFT_KAGGLE_META_MODULE_SPEC_v0`

The released specialization that `V43` should generalize from rather than reopen is:

- `docs/ARCHITECTURE_ADEU_ARC_AGI_v0.md`
- `docs/DRAFT_V42_ARC_AGI_PARTICIPATION_DECOMPOSITION_v0.md`
- released `V42-A` through `V42-G4` lock bundle on `main`

## Planning Boundary

- no reopening of released `V41` or released `V42-A`..`V42-G4` contracts is authorized
  by this planning draft;
- no claim that Kaggle is the family rather than the first host adapter is authorized by
  this planning draft;
- no lock-level schema authority is created by the candidate artifact names above;
- no autonomous submission engine, unrestricted browser/UI execution, or generalized
  multi-contest orchestration is authorized by this planning draft;
- no blanket claim that reasoning AI is the dominant leverage surface for all contests is
  authorized by this planning draft;
- no promotion from contest-world compilation into strategy or execution lanes is
  authorized without later decomposition and lock-level gating.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "next_arc_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v25.md",
  "baseline_arc": "vNext+98",
  "closed_prior_family": "V42",
  "closed_prior_paths": [
    "V42-A",
    "V42-B",
    "V42-C",
    "V42-D",
    "V42-E",
    "V42-F",
    "V42-G1",
    "V42-G2",
    "V42-G3",
    "V42-G4"
  ],
  "active_family": "V43",
  "active_family_status": "candidate_selected_not_started_external_governed_contest_participation",
  "closed_current_family_paths": [],
  "planned_current_family_paths": [
    "V43-A",
    "V43-B",
    "V43-C",
    "V43-D",
    "V43-E",
    "V43-F"
  ],
  "default_next_arc_candidate": "V43-A",
  "default_next_concrete_arc_candidate": "vNext+99",
  "family_architecture_doc": "docs/DRAFT_CONTEST_PARTICIPATION_MODULE_SPEC_v0.md",
  "family_decomposition_doc": "not_selected_yet",
  "planned_family_packages": [
    "packages/adeu_contest"
  ],
  "first_slice_active_packages": [
    "packages/adeu_contest"
  ],
  "challenge_reference": "external_governed_contests",
  "first_host_adapter_candidate": "Kaggle",
  "prior_domain_specific_specialization": "ARC-AGI-3",
  "host_adapter_first_class_required": true,
  "host_truth_boundary_required": true,
  "observed_vs_inferred_separation_required": true,
  "ambiguous_legality_fail_closed_required": true,
  "public_score_non_authoritative_required": true,
  "contest_archetype_and_leverage_map_non_equivalent_required": true,
  "contest_archetype_and_leverage_map_named_family_invariant_required": true,
  "first_family_priority": "contest_world_compilation_before_broad_execution",
  "v43abc_staged_realization_of_seed_first_safe_family_shape_required": true,
  "v43a_contest_packet_required": true,
  "v43a_initial_host_adapter_required": true,
  "v43a_contest_packet_minimum_identity_contract_required": true,
  "v43b_rule_eval_resource_timeline_surfaces_required": true,
  "v43c_archetype_leverage_map_required": true,
  "v43d_lawful_strategy_catalog_planned": true,
  "v43e_strategy_selection_posture_planned": true,
  "v43f_execution_evidence_postmortem_planned": true,
  "full_autonomous_submission_engine_initially_deferred": true,
  "unrestricted_ui_browser_execution_initially_deferred": true,
  "generalized_multi_contest_orchestration_initially_deferred": true,
  "planning_boundary_mode": "scope_guard_not_lock_authority",
  "authority_layering_note": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
  "horizon_glossary_note": "docs/DRAFT_INTENT_HORIZON_GLOSSARY_v0.md",
  "future_seam_promotion_rules_note": "docs/DRAFT_FUTURE_SEAM_PROMOTION_RULES_v0.md",
  "next_family_decomposition_required_before_lock": true
}
```
