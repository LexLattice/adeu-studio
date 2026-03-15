# Draft Next Arc Options v10 (Post vNext+64, Post V36-D Closure)

This document defines the post-`vNext+64` planning baseline for the next ADEU-governed
implementation family.

Status: active planning draft (`V34`, `V35`, `V36-A`, `V36-B`, `V36-C`, and `V36-D`
closed; next
path selection in progress).

Goal:

- carry forward the completed `V34` trust/distribution line without reopening it;
- carry forward the completed `V35-A` through `V35-E` orchestration/delegation/
  visibility/topology/enforcement line without widening it implicitly;
- shift the next family from execution constitution into typed UX governance and surface
  compilation;
- turn the seed concept of UX as ADEU-governed constitutional order into an actual
  implementation roadmap;
- make surface generation artifact-first rather than prompt-first:
  `ux_domain_packet@1` -> `ux_morph_ir@1` -> `ux_surface_projection@1` ->
  `ux_interaction_contract@1` -> `ux_morph_diagnostics@1`;
- make lawful UX variability explicit by separating invariant surface law from morphable
  surface form;
- make it explicit that UI artifacts may express authority but may not mint authority:
  surface arrangement may expose or suppress already-governed actions only within accepted
  bounds, and may not create new execution authority, weaken existing gates, or promote
  advisory material into authoritative action by placement or emphasis;
- start on ADEU Studio's native terrain with one bounded
  `artifact_inspector_advisory_workbench` family rather than a generic "design system"
  release.

This is a planning document only. It is not a lock doc and does not authorize runtime
behavior or UI behavior changes.

## Inputs

- `docs/DRAFT_NEXT_ARC_OPTIONS_v9.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS60.md`
- `docs/ASSESSMENT_vNEXT_PLUS60_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
- `docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`
- `docs/ASSESSMENT_vNEXT_PLUS63_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md`
- `docs/ASSESSMENT_vNEXT_PLUS64_EDGES.md`
- `docs/seed arc v10.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

## Baseline Agreement (Current Ground Truth)

- Baseline implementation is `vNext+64` (`V36-D`) on `main`.
- `V34-A` through `V34-G`, `V35-A` through `V35-E`, and `V36-A` through `V36-D` are
  closed.
- `stop_gate_metrics@1` remains the active stop-gate schema family.
- Stop-gate metric-key cardinality baseline remains `80` (derived from `metrics` object
  keys only).
- Determinism/replayability, canonical JSON hashing, and fail-closed posture remain
  mandatory.
- The execution constitution is no longer hypothetical:
  `V35-A` through `V35-E` already froze canonical orchestration state, delegated worker
  handoffs, transcript/progress visibility, topology duty maps, and bounded runtime
  enforcement.
- `apps/web` already contains user-facing artifact/evidence/copilot surfaces, but the repo
  does not yet have a typed UX-governance artifact family for compiling those surfaces
  from explicit ADEU contracts.
- The current `apps/web` surfaces were built by conventional component composition rather
  than canonical UX-governance artifacts:
  `artifacts/`, `concepts/`, `copilot/`, `evidence-explorer/`, `explain/`, `papers/`, and
  `puzzles/` should be treated as baseline terrain, not as proof that V36 foundations
  already exist.
- The seed for this next family is explicit:
  UX should be treated as typed ADEU governance over user cognition/action rather than as
  ad hoc component styling or generic "modern dashboard" prompting.
- The first bounded terrain proposed by the seed is native to ADEU Studio:
  `artifact_inspector_advisory_workbench`.
- The greenfield `V36-A` substrate now exists on `main`:
  canonical `ux_domain_packet@1`,
  canonical `ux_morph_ir@1`,
  one accepted bound reference-instance pair,
  the frozen first-family approved profile table,
  the frozen same-context reachability glossary,
  and canonical `v36a_ux_domain_morph_ir_evidence@1`.
- The greenfield `V36-B` substrate now exists on `main`:
  canonical `ux_surface_projection@1`,
  canonical `ux_interaction_contract@1`,
  one accepted bound projection/interaction reference pair,
  explicit authority provenance resolution,
  stable provenance hooks,
  stable implementation-observable bindings,
  and canonical `v36b_surface_projection_interaction_evidence@1`.
- The greenfield `V36-C` rendered reference surface now exists on `main`:
  one bounded `artifact_inspector_advisory_workbench` route,
  one rendered route contract,
  one semantic snapshot,
  one implementation binding manifest,
  and canonical `v36c_artifact_inspector_reference_surface_evidence@1`.
- The greenfield `V36-D` diagnostics/conformance lane now exists on `main`:
  canonical `ux_morph_diagnostics@1`,
  canonical `ux_conformance_report@1`,
  one accepted deterministic diagnostics artifact,
  one accepted deterministic conformance report,
  a frozen conformance aggregation rule,
  and canonical `v36d_morph_diagnostics_conformance_evidence@1`.
- No released `V36-E` surface-compiler export or lawful-variant implementation exists yet
  in the repo; the remaining `V36` path should continue to prefer explicit new
  foundations over ad hoc accretion into existing page components.
- The closeout hardening bundle exists as a separate operational proposal only:
  - `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- The Copilot/Codex CLI approval-flag drift remains a separate future-cleanup item and is
  not implicitly folded into this new family.

## Planning Boundary (For This Family)

- No solver/runtime semantics contract change is authorized by this planning draft.
- No implicit reopening of the closed `V35` authority, delegation, visibility, topology,
  or enforcement surfaces is authorized.
- No user/worker authority boundary change is authorized by UI affordance alone.
- No direct code generation from free-form product brief is authorized in this family
  without an intervening typed UX artifact layer.
- No generic design-system release, theme/palette program, or "make it more modern"
  iteration loop is recommended as primary scope.
- No silent merging of advisory and authoritative actions is permitted.
- No surface may present provisional, estimated, or advisory state as authoritative by
  style or placement alone.
- Salience-bearing surfaces must be specifiable in measurable terms suitable for later
  rendered-surface conformance checks;
  CSS/theme choices may not nullify required evidence, status, warning, or diagnostic
  salience while leaving the canonical artifacts nominally unchanged.
- Morph variation must preserve explicit invariant law:
  evidence visibility, trust boundaries, deontic gating, and state feedback may not drift
  under layout/style variation.
- Required evidence visibility must be operationalized for the first family:
  required evidence must be reachable in the same bounded workbench context without route
  change and without passing through a destructive or committing action.
- Runtime event streams, worker prose, and UI-local summaries remain non-authoritative by
  themselves unless explicit future lock text says otherwise.
- UX-governance/schema/compiler logic should prefer an explicit artifact layer or dedicated
  package rather than being buried ad hoc in page components by default.
- No implicit rewrite of unrelated existing `apps/web` routes is authorized by this family;
  the first reference surface should land as a bounded new surface or explicitly bounded
  extension rather than a silent repo-wide UI retrofit.
- The closeout hardening bundle remains a separate operational track and is not implicitly
  folded into the next UX-governance family unless explicitly locked later.

## Naming Convention (New Family)

- `V36-*` identifiers are reserved for the next UX-governance / surface-compiler family.
- `B36-*` identifiers are reserved for explicit multi-path bundles if later needed.
- `V35-*` remains historical/closed and is not reused.

## Family Scale Note

- `V36` currently defines `5` paths (`V36-A` through `V36-E`) with a default sequential
  planning span of `vNext+61` through `vNext+65`.
- This sequence is planning intent only; each arc still requires explicit lock/assessment/
  decision docs before implementation authority is granted.

## Vision Contract (Planning-Level)

- Authoritative sources:
  - ADEU governance docs and accepted evidence artifacts;
  - canonical UX-governance artifacts if this family is implemented:
    `ux_domain_packet@1`,
    `ux_morph_ir@1`,
    `ux_surface_projection@1`,
    `ux_interaction_contract@1`,
    `ux_morph_diagnostics@1`,
    and any later explicitly locked conformance report;
  - already-accepted execution-state/visibility/topology/enforcement artifacts from the
    closed `V35` line when a surface needs authoritative runtime context.
- Non-authoritative sources:
  - free-form "nice UI" prompts by themselves;
  - aesthetic-only layout proposals not backed by canonical UX artifacts;
  - worker prose or event streams by themselves;
  - UI-local summaries that are not backed by canonical artifacts;
  - visual emphasis that implies authority, certainty, or reversibility not present in the
    typed contract.
- Operational rule:
  - Codex should not design from vibes;
  - it should compile a surface from explicit ontology, epistemics, deontics, and utility
    constraints;
  - lawful morph variation is allowed only within approved morph axes;
  - invariant law must survive all valid morphs;
  - the first production terrain should be one bounded ADEU-native workbench surface, not
    a broad product-wide redesign.

## Machine-Checkable Planning Baseline

```json
{
  "schema": "adeu_surface_planning_baseline@1",
  "source_baseline_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v9.md",
  "closed_path_families": [
    "V34",
    "V35"
  ],
  "closed_paths": [
    "V34-A",
    "V34-B",
    "V34-C",
    "V34-D",
    "V34-E",
    "V34-F",
    "V34-G",
    "V35-A",
    "V35-B",
    "V35-C",
    "V35-D",
    "V35-E",
    "V36-A",
    "V36-B",
    "V36-C",
    "V36-D"
  ],
  "next_path_family": "V36",
  "v36_path_count": 5,
  "v36_default_arc_span": {
    "from": "vNext+61",
    "to": "vNext+65"
  },
  "default_next_arc_candidate": "V36-E",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality_baseline": 80,
  "no_implicit_metric_key_expansion": true,
  "artifact_authority_model": "canonical_artifacts_only",
  "control_execution_split": {
    "control_plane": "accepted_governance_artifacts",
    "execution_plane": "bounded_worker_implementation"
  },
  "surface_generation_mode": "artifact_first_surface_compilation",
  "surface_compiler_foundation_status": "greenfield",
  "bounded_reference_surface_family": "artifact_inspector_advisory_workbench",
  "existing_web_surface_governance_status": "conventional_component_composition_without_typed_ux_artifacts",
  "reference_surface_rollout_policy": "prefer_new_bounded_route_or_explicitly_bounded_surface_over_rewriting_unrelated_existing_routes",
  "surface_compilation_units": [
    "surface_root",
    "bounded_workbench",
    "region",
    "lane",
    "action_cluster"
  ],
  "top_level_ux_artifacts": [
    "ux_domain_packet@1",
    "ux_morph_ir@1",
    "ux_surface_projection@1",
    "ux_interaction_contract@1",
    "ux_morph_diagnostics@1",
    "ux_conformance_report@1"
  ],
  "adeu_split_required": [
    "ontology",
    "epistemics",
    "deontics",
    "utility"
  ],
  "invariant_morph_split_required": true,
  "allowed_morph_axes": [
    "density",
    "navigation_mode",
    "information_posture",
    "interaction_tempo",
    "salience_posture",
    "state_exposure",
    "command_posture"
  ],
  "default_reference_morph_profile": {
    "density": "high",
    "navigation_mode": "split_pane",
    "information_posture": "evidence_first",
    "interaction_tempo": "expert_fast_path",
    "salience_posture": "evidence_and_status_prominent",
    "state_exposure": "full_explicit",
    "command_posture": "dual_lane"
  },
  "epistemic_state_enum": [
    "loading",
    "draft",
    "candidate",
    "validated",
    "authoritative",
    "conflicted",
    "stale",
    "ambiguous"
  ],
  "utility_ranking_required": true,
  "advisory_authoritative_boundary_explicit": true,
  "evidence_visibility_before_commit_required": true,
  "required_evidence_visibility_rule": "required_evidence_must_be_reachable_in_same_bounded_workbench_context_without_route_change_and_without_passing_through_commit_or_destructive_action",
  "same_context_reachability_glossary": {
    "same_context_reachable": [
      "scroll_within_current_bounded_workbench",
      "expand_or_collapse_inline_disclosure_within_current_bounded_workbench",
      "switch_nonrouting_tab_within_current_bounded_workbench",
      "open_or_close_noncommitting_drawer_within_current_bounded_workbench"
    ],
    "context_change": [
      "route_change",
      "leave_current_bounded_workbench",
      "open_detached_surface_that_replaces_current_bounded_workbench_context"
    ],
    "disallowed_reachability_path": [
      "pass_through_commit_action",
      "pass_through_destructive_action",
      "require_navigation_to_different_route"
    ]
  },
  "salience_constraints_must_be_measurable": true,
  "rendered_surface_conformance_hooks_required": true,
  "no_free_form_ui_codegen_without_ir": true,
  "no_visual_authority_inflation": true,
  "ui_artifacts_may_express_but_may_not_mint_authority": true,
  "authoritative_gate_source_policy": "must_resolve_only_to_accepted_governance_artifacts_or_already_accepted_v35_runtime_authority_artifacts_not_page_local_constants_route_config_or_ad_hoc_component_logic",
  "first_family_profile_table_required": true,
  "first_family_profile_cardinality": 2,
  "profile_combination_policy": "combinations_outside_explicitly_enumerated_first_family_profiles_invalid_even_if_axis_values_are_individually_allowed",
  "surface_compiler_placement_policy": "avoid_burying_ux_governance_logic_directly_in_page_components_without_explicit_artifact_layer",
  "runtime_context_truth_policy": "runtime_events_and_worker_prose_are_source_surfaces_only_not_accepted_truth_without_canonical_artifact_backing_or_explicit_governance_acceptance",
  "closeout_hardening_bundle_status": "separate_operational_proposal_only"
}
```

## Path V36-A: UX Domain Packet and Morph IR Baseline

Lock class: `L1`

Status note:

- closed on `main` via `vNext+61`; treat this path as released substrate, not as an open
  implementation candidate.

Goal:

- make UX governance explicit as typed ADEU artifacts rather than prose prompt style.

Scope:

- define canonical `ux_domain_packet@1` for bounded ADEU Studio surface planning:
  - domain,
  - user archetypes,
  - tasks,
  - risk level,
  - environment/device assumptions,
  - latency assumptions,
  - trust sensitivity,
  - reversibility of actions,
  - required evidence visibility,
  - utility ranking;
- define canonical `ux_morph_ir@1` as invariant UX structure independent of concrete
  component/CSS implementation;
- require explicit O/E/D/U separation in the IR:
  - ontology,
  - epistemics,
  - deontics,
  - utility;
- freeze the invariant vs morphable split for the first family:
  - invariant examples:
    evidence-before-commit visibility,
    trust-boundary clarity,
    destructive-action gating,
    observable state transitions,
    unambiguous primary action;
  - morphable examples:
    nav placement,
    region arrangement,
    disclosure style,
    component topology within approved bounds;
- freeze initial morph-axis vocabulary sufficient for controlled lawful variation:
  - `density`,
  - `navigation_mode`,
  - `information_posture`,
  - `interaction_tempo`,
  - `salience_posture`,
  - `state_exposure`,
  - `command_posture`;
- define `salience_posture` constitutionally rather than aesthetically:
  it governs evidence salience, action salience, status salience, and diagnostic salience,
  not open-ended beauty/style taste;
- require first-family salience rules to be expressible in measurable implementation-facing
  terms suitable for later rendered-surface conformance checks rather than prose-only
  style intent;
- freeze the first-family evidence-before-commit invariant operationally:
  required evidence must be reachable in the same bounded workbench context without route
  change and without passing through a destructive or committing action;
- freeze the first-family reachability glossary:
  - same-context reachable:
    scroll within the current bounded workbench,
    expand/collapse inline disclosure,
    switch a non-routing tab,
    open/close a non-committing drawer;
  - context change:
    route change,
    leaving the bounded workbench,
    opening a detached surface that replaces the current workbench context;
  - disallowed reachability path:
    passing through a commit action,
    passing through a destructive action,
    requiring navigation to a different route;
- freeze the first-family approved profile table:
  combinations outside the explicitly enumerated approved profiles are invalid even if
  built from individually allowed axis values;
- anchor the first domain family to `artifact_inspector_advisory_workbench`.

Locks:

- no surface implementation release is authorized in this path by default;
- no generic design-system or palette/tokens program is authorized in this path;
- no direct brief-to-code path is valid without `ux_domain_packet@1` and `ux_morph_ir@1`;
- no advisory/authoritative boundary may be implicit in the schema;
- `V36-A` is not complete with schema prose alone:
  one canonical filled reference instance for
  `artifact_inspector_advisory_workbench` must be serializable and hashable;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- canonical `ux_domain_packet@1` schema and `ux_morph_ir@1` schema exist;
- vocabularies, enums, and first-family morph-axis/value sets required for the bounded
  reference terrain are frozen;
- the first-family reachability glossary and approved profile table are frozen;
- one accepted `artifact_inspector_advisory_workbench` reference instance exists for both
  schemas and can be serialized canonically and hashed deterministically;
- the accepted reference instance is sufficient to describe one bounded ADEU-native
  surface family deterministically, including invariant law, allowed morph range, trust
  boundaries, and utility ordering.

## Path V36-B: Surface Projection and Interaction Contract Baseline

Lock class: `L1`

Status note:

- closed on `main` via `vNext+62`; treat this path as released substrate, not as an open
  implementation candidate.

Goal:

- turn the morph IR into a deterministic surface projection and typed action/state graph.

Scope:

- define canonical `ux_surface_projection@1` for the bounded surface family:
  - page/workbench topology,
  - region layout,
  - component placement,
  - responsive behavior,
  - state-specific rendering,
  - evidence placement,
  - action placement,
  - trust-surface placement;
- define canonical `ux_interaction_contract@1`:
  - surface_event,
  - ui_transition,
  - preconditions,
  - user-visible consequence,
  - requested_runtime_effect,
  - runtime-visible consequence,
  - authoritative_gate_source,
  - reversible?,
  - confirmation required?,
  - evidence required?,
  - rollback path,
  - failure surface,
  - success surface;
- require `authoritative_gate_source` to resolve only to:
  - accepted governance artifacts, or
  - already-accepted `V35` runtime authority artifacts;
- forbid `authoritative_gate_source` from resolving to:
  - page-local constants,
  - UI route configuration,
  - ad hoc component logic;
- require projection to distinguish explicitly:
  - advisory actions,
  - authoritative actions,
  - commit/approval gates,
  - provisional vs authoritative state;
- require surface projection and interaction contract outputs to preserve stable provenance
  hooks plus stable implementation-observable bindings for later
  `ux_morph_diagnostics@1` and any later conformance report;
- make the authority boundary explicit:
  `ux_surface_projection@1` and `ux_interaction_contract@1` may place, expose, or hide
  already-governed actions only within accepted bounds;
  they may not mint new execution authority, weaken an existing gate, or promote advisory
  material into authoritative action by arrangement or emphasis alone;
- require projection/state rendering to stay derived from `ux_morph_ir@1` rather than
  page-local improvisation;
- keep the first reference morph anchored to an expert, evidence-first,
  split-pane-capable workbench profile.

Locks:

- no runtime enforcement of the interaction contract is required in this path yet;
- no direct mutation of deontic meaning by style/layout variation is allowed;
- projection output must not hide required evidence behind secondary regions by default;
- the first family must operationalize "evidence before commit" using the shared planning
  rule:
  same bounded workbench context, no route change, no commit/destructive action required
  to reach required evidence;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- one deterministic `ux_surface_projection@1` plus `ux_interaction_contract@1` pair can be
  derived from the canonical morph IR for the bounded workbench family without collapsing
  advisory vs authoritative meaning;
- the derived pair preserves explicit authority provenance through valid
  `authoritative_gate_source` resolution and exposes stable provenance/binding surfaces
  sufficient for later diagnostics and rendered-surface conformance.

## Path V36-C: Artifact Inspector / Advisory Workbench Reference Surface

Lock class: `L0`

Status note:

- closed on `main` via `vNext+63`; treat this path as released rendered substrate, not
  as an open implementation candidate.

Goal:

- implement one bounded ADEU-native reference surface from the typed UX artifacts.

Scope:

- build one `artifact_inspector_advisory_workbench` surface over existing ADEU Studio
  terrain:
  - source artifact,
  - proposed artifact or candidate variant,
  - diagnostics lane,
  - evidence lane,
  - trust/status lane,
  - advisory action lane,
  - explicit commit gate or handoff boundary;
- land the first reference surface as a bounded new route or explicitly bounded surface in
  `apps/web`, adjacent to existing artifact/evidence/copilot terrain rather than as a
  broad rewrite of unrelated routes;
- make the surface derived from canonical `ux_surface_projection@1` and
  `ux_interaction_contract@1` rather than ad hoc component composition only;
- preserve explicit epistemic rendering for:
  - loading,
  - draft,
  - candidate,
  - validated,
  - authoritative,
  - conflicted,
  - stale,
  - ambiguous;
- preserve explicit advisory vs authoritative rendering and existing ADEU authority
  boundaries;
- preserve stable provenance hooks for later `ux_morph_diagnostics@1` rather than forcing
  diagnostics to reconstruct state from page-local heuristics after the fact;
- preserve stable implementation-observable bindings for later rendered-surface conformance
  checks over critical gates, disabled states, evidence reachability, and salience-bearing
  surfaces;
- make the authority boundary explicit:
  the reference surface may express already-governed authority but may not mint authority,
  weaken gates, or promote advisory material into authoritative action by salience or
  placement alone;
- keep the initial implementation narrow:
  no product-wide redesign, no broad navigation overhaul, no replacement of unrelated
  pages.

Locks:

- the reference surface is bounded and does not imply a repo-wide design-system release;
- the reference surface does not imply an implicit rewrite of existing `artifacts/`,
  `concepts/`, `copilot/`, `evidence-explorer/`, `explain/`, `papers/`, or `puzzles/`
  routes;
- the surface must not visually imply governance authority beyond already-accepted ADEU
  control boundaries;
- no silent merging of evidence, diagnostics, and commit surfaces into one undifferentiated
  lane is allowed;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- the user can inspect one bounded reference workbench compiled from the UX artifact stack
  while evidence visibility, trust calibration, and action authority remain explicit;
- the implemented surface is traceable back to canonical
  `ux_surface_projection@1` / `ux_interaction_contract@1` artifacts and exposes the stable
  implementation-observable bindings required for later diagnostics and rendered-surface
  conformance.

## Path V36-D: Morph Diagnostics and Conformance Baseline

Lock class: `L1`

Goal:

- make UX-law violations explicit instead of discovering them only by manual taste review.

Scope:

- define canonical `ux_morph_diagnostics@1`;
- freeze a minimum diagnostics severity taxonomy:
  - `error`
  - `warning`
  - `advisory`
- define canonical `ux_conformance_report@1` to separate raw diagnostics from final
  conformance judgment and to bridge canonical artifacts into rendered-surface assertions
  for critical gates and salience-bearing surfaces;
- freeze a deterministic conformance aggregation rule for the first bounded family:
  - any `error` => `fail`,
  - no `error` and at least one `warning` => `needs_review`,
  - only `advisory` findings or no findings => `pass`;
- require each diagnostic finding to carry at least:
  - stable `finding_id`,
  - stable `violation_family`,
  - `severity`,
  - provenance pointers,
  - rendered-surface assertion inputs actually used,
  - supporting evidence refs,
  - conformance impact;
- require the conformance report to carry at least:
  - `overall_judgment`,
  - supporting finding ids,
  - severity counts,
  - failed / warning rule families,
  - reference binding fields,
  - derivation metadata proving it was derived from diagnostics plus frozen
    rendered-surface assertions;
- detect bounded first-family violations such as:
  - destructive action lacks adequate confirmation,
  - provisional data rendered with authoritative styling,
  - required evidence not reachable within the same bounded workbench context,
  - utility target conflicts with density/posture,
  - requested interaction profile conflicts with realized command grammar against the
    frozen approved profile contract,
  - competing primary actions in one region,
  - failure mode lacks visible recovery path,
  - advisory/authoritative boundary visually collapsed;
- require diagnostics to trace back to the canonical domain/morph/projection/interaction
  artifacts rather than free-form critique text;
- require each diagnostic to carry provenance pointers into the canonical artifact stack
  so the output remains typed and auditable rather than prose-like.
- require the rendered-surface assertion bridge to stay grounded in the frozen rendered
  artifact inputs and to avoid introducing fresh route-local heuristic truth sources.

Locks:

- diagnostics are constitutional/audit surfaces first, not aesthetic taste engines;
- no purely visual variant may pass if it changes deontic meaning or trust-boundary
  meaning;
- no runtime auto-repair or self-mutating UI behavior is authorized in this path;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- deterministic diagnostics exist for the first bounded workbench family and can surface
  seeded UX-law violations with provenance into the canonical artifact stack;
- overall conformance judgment is deterministically derived from the accepted diagnostics
  artifact according to the frozen aggregation rule rather than local interpretation.

## Path V36-E: Surface Compiler Export and Controlled Variant Range

Lock class: `L1`

Goal:

- make Codex operate as a bounded surface compiler rather than a designer-from-scratch for
  the first family.

Scope:

- define canonical `ux_surface_compiler_export@1`;
- define canonical `ux_surface_compiler_variant_manifest@1`;
- implement one deterministic builder pipeline from typed brief/domain packet through:
  - `ux_domain_packet@1`,
  - `ux_morph_ir@1`,
  - `ux_surface_projection@1`,
  - `ux_interaction_contract@1`,
  - `ux_morph_diagnostics@1`,
  - `ux_conformance_report@1`;
- support controlled lawful variation for the bounded workbench family along approved
  morph axes only;
- freeze allowed value sets for the approved axes in the first compiler release;
- freeze the explicit approved profile table for the first compiler release:
  combinations outside that table are invalid even if composed from individually allowed
  axis values;
- limit the first release to a finite approved variant range:
  one canonical reference profile plus one alternate lawful profile, not open-ended
  combination-space exploration;
- require the alternate lawful export to earn its own deterministic diagnostics and
  conformance evaluation under the frozen `V36-D` conformance report structure and
  aggregation rule before emission;
- emit implementation-facing contracts sufficient to drive bounded React/component
  realization without reintroducing free-form prompt interpretation at the last mile;
- require `ux_surface_compiler_export@1` to carry at least:
  - binding tuple,
  - source artifact references,
  - approved profile id,
  - implementation target payloads,
  - exported provenance-hook map,
  - exported implementation-binding map,
  - conformance-gating reference,
  - derivation metadata;
- require `ux_surface_compiler_variant_manifest@1` to carry at least:
  - reference binding tuple,
  - canonical versus alternate designation,
  - stable export artifact refs,
  - target-domain coverage per profile,
  - source artifact hashes / derivation refs,
  - per-profile conformance-gating result;
- require all approved variants to preserve:
  - invariant law,
  - evidence-before-commit visibility,
  - advisory/authoritative distinction,
  - deontic gating,
  - observable state feedback;
- keep the variant range bounded:
  no broad multi-product surface compiler release, no style-only variant tournament, no
  unconstrained "modernize the UI" loop.

Locks:

- variant generation may not widen the allowed morph-axis vocabulary without an explicit
  future lock;
- variant generation may not widen allowed axis value sets or approved profile count
  without an explicit future lock;
- implementation exports must remain derived from canonical UX artifacts, not side-channel
  prompts;
- side-channel prompt or local-heuristic inputs must be rejected rather than accepted as
  last-mile compiler truth;
- implementation exports may not rely on unconstrained CSS/theme overrides that weaken
  required salience, hide required evidence, or visually neutralize diagnostic severity;
- `css_token_map` is a bounded implementation mapping for this family only and does not
  authorize a generalized token system, theme program, or palette expansion;
- no variant may pass if diagnostics show deontic, epistemic, or trust-boundary drift;
- pass gating in this path must consume the frozen `V36-D` conformance report structure
  and aggregation rule rather than export-local heuristics;
- no new stop-gate metric keys are authorized in this path unless explicitly released in
  the corresponding lock doc.

Acceptance:

- for one bounded ADEU-native workbench family, the repo can produce one canonical surface
  plus one explicitly approved alternate lawful profile from typed UX artifacts without
  deontic or trust-boundary drift, with both profiles independently pass-gated by the
  frozen `V36-D` conformance rule;
- combinations outside the frozen first-family approved profile table remain invalid even
  if their individual axis values are otherwise allowed.

## Separate Operational Track (Non-V36)

The closeout hardening bundle remains separately named and intentionally orthogonal:

- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`

It should not be treated as implicit `V36` scope unless later formalized under its own lock
bundle. The current recommendation remains:

1. `O1` closeout orchestration extraction
2. `O2` closeout artifact index + lint
3. `O3` advisory adjudication scaffold

## Recommended Default Order

1. `V36-A`
   - freeze the typed UX-governance substrate first:
     domain packet, morph IR, invariant/morphable split, and morph-axis vocabulary.
2. `V36-B`
   - freeze projection and interaction contracts before broad UI implementation work.
3. `V36-C`
   - implement one bounded ADEU-native reference workbench from the canonical artifacts.
4. `V36-D`
   - make UX-law diagnostics deterministic and provenance-linked once the reference
     workbench exists.
5. `V36-E`
   - only then widen into controlled lawful variant generation and implementation export.

## Non-Goals (Current Family)

This planning draft does not recommend:

- generic text-to-UI generation from free-form briefs alone;
- a repo-wide design-system or theme overhaul as the primary deliverable;
- reopening `V35` execution constitution surfaces under a UI planning label;
- automatic acceptance, closeout, or worker-authority promotion via interface design;
- treating event streams, prose summaries, or visual polish as substitutes for canonical
  UX artifacts;
- unconstrained aesthetic variant generation;
- replacement of existing ADEU authority boundaries with "friendly" UI abstractions that
  hide trust, evidence, or gating semantics.

## Recommendation

- select `V36-E` as the next default candidate after the closed `V36-D`
  diagnostics/conformance baseline;
- keep the next release artifact-first and constitutional:
  ship deterministic surface-compiler export and one bounded lawful alternate profile
  over the released diagnostics/conformance substrate rather than widening into a broad
  style or design-system program;
- preserve the seed's core design rule:
  Codex should compile a lawful surface from O/E/D/U artifacts, not improvise a dashboard
  from vibes;
- keep the first implementation terrain narrow and ADEU-native:
  `artifact_inspector_advisory_workbench`;
- preserve the separate operational cleanup track (`O1`/`O2`/`O3`) as a distinct follow-on
  rather than silently mixing it into the new UX-governance family.
