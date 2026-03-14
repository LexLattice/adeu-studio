# Locked Continuation vNext+62 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/seed arc v10.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 14, 2026 UTC).

## Decision Basis

- `vNext+61` (`V36-A`, `A1`/`A2`) is merged on `main` with green CI checks.
- `vNext+61` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md` marks the `V36-A` substrate edge set as closed
  and restores eligibility for the next thin `V36` path.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` now names `V36-B` as the next default candidate
  after `V36-A` closure.
- current repo reality is narrower than a full projection-to-surface lane:
  - canonical `ux_domain_packet@1`, `ux_morph_ir@1`, one accepted bound reference pair,
    the first-family approved profile table, and the same-context reachability glossary
    now exist on `main`,
  - no released `ux_surface_projection@1` or `ux_interaction_contract@1` implementation
    exists on `main`,
  - no released projection-level stable provenance hooks or implementation-observable
    binding lane exists on `main`,
  - no released rendered reference workbench, diagnostics/conformance engine, or surface
    compiler export exists on `main`,
  - no released route-level UX rewrite authority or broad `apps/web` retrofit authority
    exists on `main`.
- `vNext+62` therefore selects one thin `V36-B` baseline slice only:
  - canonical `ux_surface_projection@1` and `ux_interaction_contract@1`,
  - one accepted deterministic reference projection/interaction pair for
    `artifact_inspector_advisory_workbench`,
  - explicit authority provenance, same-context evidence-before-commit preservation, and
    stable implementation-observable bindings for later diagnostics/conformance,
  - closeout evidence plus determinism/guard coverage,
  - no rendered route release, no diagnostics engine, and no compiler widening in this
    arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v62,
  - v62 keyset must be exactly equal to v61 keyset,
  - baseline derived cardinality at v62 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v62 is explicit and narrow:
  - this arc authorizes one `L1` UX-governance artifact lane only,
  - no `L0` rendered-surface release is authorized in this arc,
  - no `L2` compiler/variant release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35` baseline,
  - no route-level rewrite authority is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A` substrate surfaces remain frozen prerequisites and are not redefined by this
  arc.
- `V36-B` release-shape lock for v62 is frozen:
  - this arc is a typed UX-governance projection/interaction artifact baseline only,
  - the arc must consume released `V36-A` substrate artifacts rather than redefining
    them,
  - the arc must define `ux_surface_projection@1` and `ux_interaction_contract@1` plus
    one accepted deterministic reference pair only,
  - the arc must preserve explicit authority provenance and stable
    implementation-observable bindings for later diagnostics/conformance,
  - the arc must preserve the frozen same-context evidence-before-commit rule from
    `V36-A`,
  - no rendered route, diagnostics engine, conformance report, or surface compiler export
    is authorized in this arc,
  - no generic design-system release, theme program, or broad route retrofit is
    authorized in this arc,
  - UI artifacts may express authority but may not mint authority; this arc may not
    weaken any accepted `V35` authority gate by projection or interaction wording.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `B1` Canonical surface projection + interaction contract baseline (`V36-B`)
2. `B2` Projection/interaction evidence + determinism/guard suite (`V36-B`)

Out-of-scope note:

- any rendered `V36-C` reference surface work in this arc,
- any `V36-D` diagnostics/conformance work in this arc,
- any `V36-E` compiler export or lawful variant runtime in this arc,
- any repo-wide design-system, token, or theme overhaul in this arc,
- any broad rewrite of existing `apps/web` routes in this arc,
- any runtime enforcement change in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v62)

- `V36-C` artifact inspector / advisory workbench reference surface
- `V36-D` morph diagnostics + conformance baseline
- `V36-E` surface compiler export + controlled variant range
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- the Copilot/Codex CLI approval-flag UX cleanup remains deferred under
  `docs/FUTURE_CLEANUPS.md`

## V61 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md",
  "target": "V36-B-baseline",
  "required_continuity_guards": [
    "V36_A_A1_DOMAIN_MORPH_BASELINE_GREEN",
    "V36_A_A2_DOMAIN_MORPH_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v61_v36a_substrate_remains_frozen_while_v36b_projection_and_interaction_artifacts_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v62.
- this narrowed machine-checkable consumption block is v61-local only and does not weaken
  the global continuity locks declared above; v14-v61 baseline continuity remains in
  force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V36-B Surface Projection and Interaction Contract (Machine-Checkable)

```json
{
  "schema": "v36b_surface_projection_interaction_contract@1",
  "target_arc": "vNext+62",
  "target_path": "V36-B",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v10.md",
    "seed_source_doc": "docs/seed arc v10.md",
    "v36a_domain_morph_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md#v36a_ux_domain_morph_ir_contract@1",
    "v36a_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md",
    "v35e_runtime_authority_baseline": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1",
    "bounded_reference_surface_family": "artifact_inspector_advisory_workbench",
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "projection_interaction_requirements": {
    "foundation_status": "greenfield_over_released_v36a_substrate",
    "required_input_artifacts": [
      "ux_domain_packet@1",
      "ux_morph_ir@1",
      "v36a_accepted_reference_instance_pair@1",
      "v36a_first_family_approved_profile_table@1",
      "v36a_same_context_reachability_glossary@1"
    ],
    "canonical_artifact_schemas": [
      "ux_surface_projection@1",
      "ux_interaction_contract@1"
    ],
    "accepted_reference_projection_required": true,
    "accepted_reference_interaction_contract_required": true,
    "projection_interaction_binding_required": true,
    "projection_interaction_binding_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id"
    ],
    "projection_interaction_must_match_released_v36a_reference_pair": true,
    "v36a_reference_pair_binding_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id"
    ],
    "surface_compilation_units_required": [
      "surface_root",
      "bounded_workbench",
      "region",
      "lane",
      "action_cluster"
    ],
    "authority_distinctions_required": [
      "advisory_actions",
      "authoritative_actions",
      "commit_or_approval_gates",
      "provisional_vs_authoritative_state"
    ],
    "authoritative_gate_source_required": true,
    "authoritative_gate_source_required_for_interaction_classes": [
      "authoritative",
      "gated",
      "committing",
      "approval_bearing"
    ],
    "authoritative_gate_source_allowed_sources": [
      "accepted_governance_artifacts",
      "already_accepted_v35_runtime_authority_artifacts"
    ],
    "authoritative_gate_source_forbidden_sources": [
      "page_local_constants",
      "ui_route_configuration",
      "ad_hoc_component_logic"
    ],
    "stable_provenance_hooks_required": true,
    "stable_provenance_hook_targets_minimum": [
      "projection_units",
      "action_clusters",
      "authority_bearing_controls",
      "evidence_bearing_regions",
      "state_distinction_surfaces"
    ],
    "implementation_observable_bindings_required": true,
    "implementation_observable_binding_targets_minimum": [
      "commit_or_approval_gates",
      "advisory_vs_authoritative_actions",
      "disabled_or_unavailable_gated_states",
      "required_evidence_reachability_anchors",
      "salience_bearing_warning_status_and_diagnostic_surfaces"
    ],
    "same_context_reachability_must_consume_v36a_glossary": true,
    "no_local_glossary_shadowing": true,
    "evidence_before_commit_rule_preserved": true,
    "requested_runtime_effect_semantics_must_be_descriptive_not_authority_minting": true,
    "runtime_visible_consequence_must_reflect_accepted_runtime_truth": true,
    "runtime_visible_consequence_must_remain_epistemic_and_not_overstate_success": true,
    "first_reference_profile_id": "artifact_inspector_reference",
    "first_reference_profile_must_exist_in_v36a_approved_profile_table": true,
    "first_reference_profile_must_be_v36a_canonical_reference_profile": true,
    "accepted_v36b_reference_pair_must_use_first_reference_profile_id": true,
    "no_page_local_projection_improvisation": true,
    "binding_identifier_stability_across_deterministic_regeneration": true,
    "no_visual_authority_inflation": true,
    "ui_artifacts_may_express_but_may_not_mint_authority": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v36b_surface_projection_interaction_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "ux_surface_projection_schema_path",
      "ux_surface_projection_schema_hash",
      "ux_interaction_contract_schema_path",
      "ux_interaction_contract_schema_hash",
      "ux_surface_projection_reference_path",
      "ux_surface_projection_reference_hash",
      "ux_interaction_contract_reference_path",
      "ux_interaction_contract_reference_hash",
      "projection_interaction_binding_verified",
      "v36a_reference_pair_binding_verified",
      "reference_profile_id_verified_against_v36a_table",
      "authoritative_gate_source_resolution_verified",
      "forbidden_authoritative_gate_sources_rejected",
      "stable_provenance_hooks_verified",
      "implementation_observable_bindings_verified",
      "binding_identifier_stability_verified",
      "advisory_authoritative_boundary_preserved",
      "no_glossary_shadowing_verified",
      "evidence_before_commit_rule_preserved",
      "runtime_visible_consequence_epistemic_boundary_preserved",
      "no_visual_authority_inflation_preserved",
      "v36a_substrate_consumed_without_drift",
      "v35_authority_baseline_unchanged",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v61",
      "notes"
    ]
  },
  "test_requirements": {
    "ux_surface_projection_schema_serialization_deterministic": true,
    "ux_interaction_contract_schema_serialization_deterministic": true,
    "reference_projection_serialization_deterministic": true,
    "reference_interaction_contract_serialization_deterministic": true,
    "projection_interaction_binding_verified": true,
    "v36a_reference_pair_binding_verified": true,
    "reference_profile_id_verified_against_v36a_table": true,
    "authoritative_gate_source_resolution_verified": true,
    "forbidden_authoritative_gate_sources_rejected": true,
    "stable_provenance_hooks_verified": true,
    "implementation_observable_bindings_verified": true,
    "binding_identifier_stability_verified": true,
    "advisory_authoritative_boundary_preserved": true,
    "no_glossary_shadowing_verified": true,
    "evidence_before_commit_rule_preserved": true,
    "runtime_visible_consequence_epistemic_boundary_preserved": true,
    "projection_derived_from_v36a_substrate_without_page_local_improvisation": true,
    "no_visual_authority_inflation_preserved": true,
    "v36a_substrate_unchanged": true,
    "v35_authority_baseline_unchanged": true
  }
}
```

Interpretive notes:

- v62 defines typed projection and interaction artifacts only; it does not yet authorize a
  rendered route, diagnostics/conformance engine, or compiler export.
- the `V36-A` same-context reachability glossary remains a consumed prerequisite in v62;
  v62 may reference it, but may not silently redefine it.
- the accepted `V36-B` reference projection and accepted `V36-B` reference interaction
  contract must bind not only to each other, but also back to the accepted released
  `V36-A` reference pair through the shared reference binding fields and canonical profile
  id.
- `requested_runtime_effect` and `runtime_visible_consequence` must remain descriptive of
  already-accepted runtime semantics and authority boundaries; they are not a substitute
  for runtime-governance truth and must not collapse requested effect and accepted effect
  into one meaning or imply successful authority execution where only a request or
  transition exists.
- `authoritative_gate_source` exists to bind surface actions back to accepted governance
  or accepted `V35` runtime authority surfaces; it must not collapse into UI-local policy
  and must be present for each authoritative, gated, committing, or approval-bearing
  interaction entry.

## B1) Canonical Surface Projection + Interaction Contract Baseline (`V36-B`)

### Goal

Make `V36-B` real as a canonical projection and typed action/state contract layer rather
than planning prose.

### Scope

- add canonical `ux_surface_projection@1` and `ux_interaction_contract@1` schemas for the
  bounded `artifact_inspector_advisory_workbench` family;
- add one accepted deterministic reference projection and one accepted deterministic
  reference interaction contract, bound together by shared `reference_surface_family`,
  `reference_instance_id`, and `approved_profile_id` fields;
- require the accepted reference projection and interaction contract to bind back to the
  released accepted `V36-A` reference pair and the canonical
  `artifact_inspector_reference` profile id rather than forming only an internally
  coherent v62 pair;
- ensure projection and interaction artifacts consume the released `V36-A` substrate
  rather than improvising page-local surface semantics;
- freeze explicit authority distinctions for advisory actions, authoritative actions,
  commit/approval gates, and provisional versus authoritative state;
- freeze stable provenance hooks required at least for projection units, action clusters,
  authority-bearing controls, evidence-bearing regions, and state-distinction surfaces;
- freeze implementation-observable bindings required at least for commit/approval gates,
  advisory versus authoritative actions, disabled or unavailable gated states, required
  evidence reachability anchors, and salience-bearing warning/status/diagnostic surfaces;
- preserve the frozen evidence-before-commit rule:
  required evidence remains reachable in the same bounded workbench context without route
  change and without passing through a committing or destructive action.

### Locks

- v62 must not widen into a rendered route or a broad `apps/web` retrofit;
- v62 must not widen into diagnostics/conformance or compiler export;
- v62 must not weaken any accepted `V35` authority gate or runtime boundary;
- v62 must not redefine the released `V36-A` approved profile table or same-context
  glossary;
- v62 must not widen into the separate closeout-hardening bundle.

### Acceptance

- one bounded typed projection/interaction layer exists on `main` with canonical schemas,
  one coherent accepted reference pair bound both internally and back to the released
  `V36-A` reference substrate, explicit authority provenance, frozen profile/glossary
  consumption without redefinition, and stable provenance/binding surfaces, all
  serializable and hashable deterministically without authority drift.

## B2) Projection/Interaction Evidence + Determinism/Guard Suite (`V36-B`)

### Goal

Make the v62 `V36-B` release closeout-grade rather than relying on schema files alone by
binding it to canonical evidence and fail-closed guard coverage.

### Scope

- materialize canonical `v36b_surface_projection_interaction_evidence@1`;
- validate schema/reference outputs against the frozen `V36-B` contract and consumed
  `V36-A` substrate;
- prove deterministic serialization and hash binding for the canonical artifacts;
- fail closed on:
  - missing accepted reference projection or interaction contract,
  - projection/interaction binding mismatch across reference artifacts,
  - mismatch between the accepted `V36-B` reference pair and the released accepted `V36-A`
    reference pair or canonical reference profile id,
  - invalid or unresolved `authoritative_gate_source`,
  - forbidden `authoritative_gate_source` sourced from UI-local policy surfaces,
  - missing stable provenance hooks,
  - missing implementation-observable bindings,
  - unstable binding identifiers under deterministic regeneration,
  - advisory/authoritative boundary collapse,
  - evidence-before-commit reachability drift against the frozen `V36-A` glossary,
  - local glossary shadowing that conflicts with the frozen `V36-A` reachability terms,
  - page-local improvisation that bypasses the released `V36-A` substrate,
  - runtime-visible consequence wording that overstates accepted runtime truth or collapses
    requested versus accepted effect,
  - authority-minting drift in the projection/interaction lane,
  - stop-gate metric-key continuity drift.

### Locks

- the `V36-B` evidence lane must not redefine semantics or widen authority surfaces;
- v62 closeout evidence must preserve exact stop-gate metric-key continuity versus v61;
- evidence/test wiring must stay pre-rendered-surface, pre-diagnostics, and pre-compiler;
- no new stop-gate metric keys or schema-family changes are authorized for this slice.

### Acceptance

- v62 closeout can prove that the `V36-B` projection/interaction layer is canonical,
  deterministic, fail-closed, and authority-preserving without widening into rendered
  routes, diagnostics, or compiler work;
- v62 closeout can prove that the accepted reference projection and interaction contract
  form one coherent bound pair, remain anchored to the released accepted `V36-A`
  reference substrate and canonical profile id, and preserve authority provenance plus
  evidence-before-commit reachability explicitly and without redefinition.

## Implementation Slices

### `B1`

Branch/PR intent:

- add the canonical surface projection + interaction contract baseline for the first
  bounded surface family.

Suggested PR title:

- `ux: add v62 b1 projection and interaction baseline`

### `B2`

Branch/PR intent:

- add canonical v62 projection/interaction closeout evidence and fail-closed guard
  coverage.

Suggested PR title:

- `ux: add v62 b2 projection interaction evidence guards`

## Exit Criteria

`vNext+62` is eligible for closeout only if:

1. `B1` and `B2` merge to `main` with green CI.
2. stop-gate schema family remains `stop_gate_metrics@1`.
3. stop-gate metric key cardinality remains exactly `80`.
4. canonical `v36b_surface_projection_interaction_evidence@1` is emitted and hash-bound.
5. canonical `ux_surface_projection@1` and `ux_interaction_contract@1` schemas plus
   their accepted reference artifacts serialize deterministically and remain coherently
   bound to each other and back to the released accepted `V36-A` reference substrate.
6. `authoritative_gate_source` resolves only to accepted governance artifacts or
   accepted `V35` runtime authority artifacts, is present on every authoritative, gated,
   committing, or approval-bearing interaction entry, and never resolves to UI-local
   policy sources.
7. stable provenance hooks and implementation-observable bindings remain explicit and
   sufficient for later diagnostics/conformance across the minimum frozen target surfaces.
8. the frozen `V36-A` same-context evidence-before-commit rule remains preserved in the
   projection/interaction layer with no glossary shadowing or conflicting local
   reachability rules.
9. no authority-minting drift, rendered-route widening, diagnostics widening, compiler
   widening, or route-retrofit release is shipped by this arc.

## Why This Arc, Not `V36-C` / `V36-D` / `V36-E` or `O1` / `O2` / `O3`

- `V36-B` is the next locked path in the new v10 family and defines the deterministic
  projection/interaction substrate that later rendered-surface, diagnostics, and compiler
  work depend on directly.
- rendered surfaces, diagnostics, and compiler export are all unsafe to lock before the
  canonical projection and interaction layer, authority provenance bindings, and
  implementation-observable hooks exist and are deterministic.
- the closeout-hardening bundle remains operationally useful but orthogonal; it should not
  replace the next unreleased path inside the `V36` family.
- keeping v62 focused on projection/interaction artifacts preserves the new sequence:
  - typed domain/morph law first (`V36-A`),
  - projection/interaction second (`V36-B`),
  - bounded rendered reference surface third (`V36-C`),
  - diagnostics/conformance fourth (`V36-D`),
  - compiler export and lawful variants fifth (`V36-E`).

## Recommendation

- lock `vNext+62` as a narrow `V36-B` projection/interaction baseline only;
- keep the arc greenfield-over-substrate, deterministic, and authority-preserving;
- require canonical projection/interaction schemas, accepted reference artifacts,
  authority provenance, and stable implementation-observable bindings before any rendered
  reference surface work;
- defer rendered surfaces, diagnostics, compiler export, and the separate
  closeout-hardening track to later locked arcs.
