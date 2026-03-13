# Locked Continuation vNext+61 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS60.md`
- `docs/ASSESSMENT_vNEXT_PLUS60_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/seed arc v10.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 14, 2026 UTC).

## Decision Basis

- `vNext+60` (`V35-E`, `E1`/`E2`) is merged on `main` with green CI checks.
- `vNext+60` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS60.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS60_EDGES.md` marks the `V35` family as closed and restores
  eligibility for a fresh post-`V35` planning lane.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` now names `V36-A` as the next default candidate
  after `V35-E` closure.
- current repo reality is narrower than a full typed surface-compiler family:
  - `apps/web` already contains user-facing surfaces (`artifacts/`, `concepts/`,
    `copilot/`, `evidence-explorer/`, `explain/`, `papers/`, `puzzles/`), but those are
    conventional component-composition surfaces rather than typed UX-governance artifacts,
  - no released `ux_domain_packet@1`, `ux_morph_ir@1`, `ux_surface_projection@1`,
    `ux_interaction_contract@1`, or `ux_morph_diagnostics@1` implementation exists on
    `main`,
  - no released approved-profile table, same-context reachability glossary, or canonical
    reference instance exists on `main`,
  - no released `V36-B` projection/interaction baseline, `V36-C` reference surface,
    `V36-D` diagnostics, or `V36-E` surface-compiler export exists on `main`,
  - no released route-level UX rewrite authority, no rendered-surface conformance lane,
    and no generic design-system release is present on `main`.
- `vNext+61` therefore selects one thin `V36-A` baseline slice only:
  - canonical `ux_domain_packet@1` and `ux_morph_ir@1` schemas,
  - one accepted bounded reference instance for
    `artifact_inspector_advisory_workbench`,
  - frozen first-family morph axes, approved profile table, and same-context reachability
    glossary,
  - closeout evidence plus determinism/guard coverage,
  - no projection/runtime surface release, no broad route rewrite, and no generic
    design-system widening in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v61,
  - v61 keyset must be exactly equal to v60 keyset,
  - baseline derived cardinality at v61 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v61 is explicit and narrow:
  - this arc authorizes one `L1` UX-governance artifact lane only,
  - no `L0` or `L2` rendered-surface release is authorized in this arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35` baseline,
  - no route-level rewrite authority is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A` release-shape lock for v61 is frozen:
  - this arc is a typed UX-governance artifact baseline only,
  - the arc must define `ux_domain_packet@1` and `ux_morph_ir@1` plus the first-family
    approved profile table and reachability glossary only,
  - the arc must include one accepted bounded reference instance for
    `artifact_inspector_advisory_workbench`,
  - the arc must prefer an explicit artifact layer or dedicated new foundation surface
    rather than burying governance logic ad hoc in page components,
  - no `ux_surface_projection@1`, `ux_interaction_contract@1`, rendered route,
    diagnostics engine, or surface compiler export is authorized in this arc,
  - no generic design-system release, theme program, or broad route retrofit is
    authorized in this arc,
  - UI artifacts may express authority but may not mint authority; this arc may not
    weaken any accepted `V35` authority gate by schema or exemplar wording.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `A1` Canonical UX domain packet + morph IR baseline (`V36-A`)
2. `A2` UX domain/morph evidence + determinism/guard suite (`V36-A`)

Out-of-scope note:

- any `V36-B` projection/interaction-contract work in this arc,
- any `V36-C` rendered reference surface in this arc,
- any `V36-D` diagnostics/conformance engine in this arc,
- any `V36-E` surface-compiler export or lawful variant runtime in this arc,
- any repo-wide design-system, token, or theme overhaul in this arc,
- any broad rewrite of existing `apps/web` routes in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v61)

- `V36-B` surface projection + interaction contract baseline
- `V36-C` artifact inspector / advisory workbench reference surface
- `V36-D` morph diagnostics + conformance baseline
- `V36-E` surface compiler export + controlled variant range
- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- the Copilot/Codex CLI approval-flag UX cleanup remains deferred under
  `docs/FUTURE_CLEANUPS.md`

## V60 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md",
  "target": "V36-A-baseline",
  "required_continuity_guards": [
    "V35_E_E1_RUNTIME_ENFORCEMENT_BASELINE_GREEN",
    "V35_E_E2_ENFORCEMENT_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v60_v35e_authority_surfaces_remain_frozen_while_v36a_typed_ux_domain_and_morph_ir_baseline_is_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v61.
- this narrowed machine-checkable consumption block is v60-local only and does not weaken
  the global continuity locks declared above; v14-v60 baseline continuity remains in force
  for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V36-A UX Domain and Morph IR Contract (Machine-Checkable)

```json
{
  "schema": "v36a_ux_domain_morph_ir_contract@1",
  "target_arc": "vNext+61",
  "target_path": "V36-A",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v10.md",
    "seed_source_doc": "docs/seed arc v10.md",
    "v35e_runtime_authority_baseline": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1",
    "existing_web_surface_governance_status": "conventional_component_composition_without_typed_ux_artifacts",
    "bounded_reference_surface_family": "artifact_inspector_advisory_workbench",
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "ux_domain_morph_requirements": {
    "foundation_status": "greenfield",
    "foundation_placement_policy": "prefer_explicit_artifact_layer_or_dedicated_new_foundation_over_ad_hoc_page_component_accretion",
    "canonical_artifact_schemas": [
      "ux_domain_packet@1",
      "ux_morph_ir@1"
    ],
    "accepted_reference_instance_required": true,
    "reference_instance_binding_required": true,
    "reference_instance_binding_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id"
    ],
    "approved_profile_table_required": true,
    "approved_profile_cardinality": 2,
    "canonical_reference_profile_id": "artifact_inspector_reference",
    "alternate_lawful_profile_id": "artifact_inspector_alternate",
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
    "same_context_reachability_glossary_required": true,
    "same_context_reachability_glossary_shape": [
      "same_context_reachable",
      "context_break",
      "forbidden_barrier",
      "commit_or_destructive_barrier"
    ],
    "same_context_reachability_glossary_abstraction_level": "substrate_terms_only_pre_projection",
    "canonical_supporting_artifacts": [
      "v36a_first_family_approved_profile_table@1",
      "v36a_same_context_reachability_glossary@1"
    ],
    "no_free_form_ui_codegen_without_ir": true,
    "no_visual_authority_inflation": true,
    "ui_artifacts_may_express_but_may_not_mint_authority": true,
    "approved_profile_combination_policy": "combinations_outside_explicitly_enumerated_first_family_profiles_invalid_even_if_axis_values_are_individually_allowed"
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v36a_ux_domain_morph_ir_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "ux_domain_packet_schema_path",
      "ux_domain_packet_schema_hash",
      "ux_morph_ir_schema_path",
      "ux_morph_ir_schema_hash",
      "ux_domain_packet_reference_path",
      "ux_domain_packet_reference_hash",
      "ux_morph_ir_reference_path",
      "ux_morph_ir_reference_hash",
      "approved_profile_table_path",
      "approved_profile_table_hash",
      "same_context_reachability_glossary_path",
      "same_context_reachability_glossary_hash",
      "adeu_split_vocabulary_frozen",
      "approved_profile_table_frozen",
      "approved_profile_cardinality_verified",
      "reference_instance_binding_verified",
      "reference_instance_required_and_present",
      "deterministic_serialization_verified",
      "no_free_form_ui_codegen_without_ir_preserved",
      "ui_artifacts_may_express_but_may_not_mint_authority_preserved",
      "v35_authority_baseline_unchanged",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v60",
      "notes"
    ]
  },
  "test_requirements": {
    "ux_domain_packet_schema_serialization_deterministic": true,
    "ux_morph_ir_schema_serialization_deterministic": true,
    "reference_instance_serialization_deterministic": true,
    "reference_instance_binding_verified": true,
    "adeu_split_vocabulary_frozen": true,
    "approved_profile_table_frozen": true,
    "approved_profile_combination_policy_enforced": true,
    "same_context_reachability_glossary_frozen": true,
    "no_free_form_ui_codegen_without_ir_preserved": true,
    "ui_artifacts_may_express_but_may_not_mint_authority_preserved": true,
    "v35_authority_baseline_unchanged": true
  }
}
```

Interpretive notes:

- v61 defines the typed UX-governance substrate only; it does not yet authorize
  `ux_surface_projection@1`, `ux_interaction_contract@1`, any rendered route, or any
  diagnostics/conformance engine.
- the first-family approved profile table must enumerate exactly two allowed profiles:
  - canonical reference profile id: `artifact_inspector_reference`
  - alternate lawful profile id: `artifact_inspector_alternate`
- the accepted `ux_domain_packet@1` reference instance and accepted `ux_morph_ir@1`
  reference instance must form one coherent pair through shared binding fields:
  `reference_surface_family`, `reference_instance_id`, and `approved_profile_id`.
- the same-context reachability glossary must remain substrate-level in v61:
  it may distinguish same-context reachability, context breaks, forbidden barriers, and
  commit/destructive barriers, but must not smuggle rendered projection/widget semantics
  into the pre-`V36-B` substrate.

## A1) Canonical UX Domain Packet + Morph IR Baseline (`V36-A`)

### Goal

Make `V36-A` real as a canonical typed UX-governance substrate instead of planning prose.

### Scope

- add canonical `ux_domain_packet@1` and `ux_morph_ir@1` schemas for the bounded
  `artifact_inspector_advisory_workbench` family;
- freeze the required O/E/D/U split, invariant/morphable split, morph-axis vocabulary,
  approved profile table, and same-context reachability glossary;
- add one accepted bounded reference instance for both schemas, bound together by shared
  `reference_surface_family`, `reference_instance_id`, and `approved_profile_id` fields;
- ensure the schemas and reference instances serialize canonically and hash
  deterministically;
- keep the substrate explicitly authority-preserving:
  UI artifacts may express but may not mint authority.

### Locks

- v61 must not widen into `ux_surface_projection@1` or `ux_interaction_contract@1`;
- v61 must not release a rendered route, generic design system, theme program, or route
  retrofit;
- v61 must not weaken any accepted `V35` authority gate or runtime boundary;
- v61 must not widen into the separate closeout-hardening bundle.

### Acceptance

- one bounded typed UX-governance substrate exists on `main` with canonical schemas,
  frozen vocabularies/glossaries/profile table, and one coherent bound reference-instance
  pair, all serializable and hashable deterministically without authority drift.

## A2) UX Domain/Morph Evidence + Determinism/Guard Suite (`V36-A`)

### Goal

Make the v61 `V36-A` release closeout-grade rather than relying on schema files alone by
binding it to canonical evidence and fail-closed guard coverage.

### Scope

- materialize canonical `v36a_ux_domain_morph_ir_evidence@1`;
- validate schema/reference-instance/profile-table/glossary outputs against the frozen
  `V36-A` contract;
- prove deterministic serialization and hash binding for the canonical artifacts;
- fail closed on:
  - missing accepted reference instance,
  - reference-instance binding mismatch across schema/reference artifacts,
  - missing O/E/D/U split or invariant/morphable separation,
  - approved profile table drift,
  - invalid cross-axis profile combinations outside the enumerated approved table,
  - same-context reachability glossary drift,
  - free-form brief-to-code bypass of the typed artifact layer,
  - authority-minting drift in the schema/reference-instance lane,
  - stop-gate metric-key continuity drift.

### Locks

- the `V36-A` evidence lane must not redefine semantics or widen authority surfaces;
- v61 closeout evidence must preserve exact stop-gate metric-key continuity versus v60;
- evidence/test wiring must stay pre-projection, pre-rendered-surface, and pre-compiler;
- no new stop-gate metric keys or schema-family changes are authorized for this slice.

### Acceptance

- v61 closeout can prove that the `V36-A` substrate is canonical, deterministic,
  fail-closed, and authority-preserving without widening into projection, diagnostics, or
  rendered-surface work;
- v61 closeout can prove that the accepted `ux_domain_packet@1` and `ux_morph_ir@1`
  reference instances are one coherent bound pair and that combinations outside the
  enumerated two-profile table fail closed.

## Implementation Slices

### `A1`

Branch/PR intent:

- add the canonical UX domain packet + morph IR baseline for the first bounded surface
  family.

Suggested PR title:

- `ux: add v61 a1 domain packet and morph ir baseline`

### `A2`

Branch/PR intent:

- add canonical v61 domain/morph closeout evidence and fail-closed guard coverage.

Suggested PR title:

- `ux: add v61 a2 domain morph evidence guards`

## Exit Criteria

`vNext+61` is eligible for closeout only if:

1. `A1` and `A2` merge to `main` with green CI.
2. stop-gate schema family remains `stop_gate_metrics@1`.
3. stop-gate metric key cardinality remains exactly `80`.
4. canonical `v36a_ux_domain_morph_ir_evidence@1` is emitted and hash-bound.
5. canonical `ux_domain_packet@1` and `ux_morph_ir@1` schemas plus their accepted
   reference instances serialize deterministically and remain coherently bound.
6. approved profile table contains exactly two explicitly enumerated profiles:
   `artifact_inspector_reference` and `artifact_inspector_alternate`, and combinations
   outside that table fail closed.
7. same-context reachability glossary remains frozen in substrate terms only.
8. no free-form brief-to-code bypass and no authority-minting drift are released by this
   arc.
9. no projection/interaction, rendered-surface, diagnostics, compiler, route-rewrite, or
   design-system widening is released by this arc.

## Why This Arc, Not `V36-B` / `V36-C` / `V36-D` / `V36-E` or `O1` / `O2` / `O3`

- `V36-A` is the first locked path in the new v10 family and defines the substrate that
  every later `V36-B` through `V36-E` slice depends on directly.
- projection, rendered surfaces, diagnostics, and compiler export are all unsafe to lock
  before the canonical artifact layer, approved profile table, and reachability glossary
  exist and are deterministic.
- the closeout-hardening bundle remains operationally useful but orthogonal; it should not
  replace the first unreleased path inside the `V36` family.
- keeping v61 focused on the artifact substrate preserves the new sequence:
  - typed domain/morph law first (`V36-A`),
  - projection/interaction second (`V36-B`),
  - bounded rendered reference surface third (`V36-C`),
  - diagnostics/conformance fourth (`V36-D`),
  - compiler export and lawful variants fifth (`V36-E`).

## Recommendation

- lock `vNext+61` as a narrow `V36-A` typed UX-governance baseline only;
- keep the arc greenfield, deterministic, and authority-preserving;
- require canonical schemas, accepted reference instances, frozen approved profiles, and a
  frozen reachability glossary before any rendered surface or compiler work;
- defer projection, interaction, rendered surfaces, diagnostics, compiler export, and the
  separate closeout-hardening track to later locked arcs.
