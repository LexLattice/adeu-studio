# Draft UX Morph Change-Scoping Walkthrough v0

Status: working draft support walkthrough (March 30, 2026 UTC).

Authority layer: support.

This document is a targeted introduction for a technically strong external reader, with a
frontend/UX bias, who wants to understand how this repo scopes a change methodically.

It does not authorize runtime behavior, schema release, or implementation by itself.

Per `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`, this walkthrough is a support doc.
That means it is useful for process discipline, review method, result-shape expectations,
and claim-posture hygiene, but it is not a replacement for the actual lock, planning, or
architecture docs.

## Purpose

The fastest way to understand the repo's method is not to start from a generic backend
artifact family. It is to start from one bounded UX case and walk the whole sequence:

- seed intent
- planning selection
- arc lock
- typed artifact release
- accepted reference fixture
- rendered surface
- diagnostics and conformance
- compiler/export
- closeout evidence

The `ux_morph` / `artifact_inspector_advisory_workbench` sequence is the best example in
the repo because it is familiar frontend terrain, but it is still governed in ADEU terms
rather than by visual taste alone.

## Reading Contract

This walkthrough uses the phrase "meta-indexed change scoping" as explanatory shorthand.
That is not the repo's primary doctrinal phrase. In repo-native terms, the method is more
often expressed as:

- locked continuations
- typed artifact families
- machine-checkable contracts
- canonical schemas and accepted fixtures
- hash-bound closeout evidence

The "meta-index" is the linked structure across those layers. A change is not scoped by a
single brief. It is scoped by an explicit chain of references:

- planning docs point to prior locks and closeout state;
- lock docs name the precise artifact family allowed in the arc;
- released artifacts carry `schema` ids;
- reference instances bind through shared fields such as
  `reference_surface_family`, `reference_instance_id`, and `approved_profile_id`;
- closeout evidence records hashes, consumed predecessors, and continuity assertions.

That is the core method.

## Controlling Sources By Authority Layer

### Architecture / decomposition

- `docs/ARCHITECTURE_ADEU_STUDIO_v0.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

These are authoritative for the conceptual frame. They explain why the repo treats docs
as semantic authority surfaces and why the semantic-compiler track exists.

### Planning

- `docs/seed arc v10.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`

These are authoritative for the family-selection posture and the current planning
boundary, but not by themselves implementation-authoritative.

### Lock

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md`

These are the implementation-authoritative docs for the `V36-A` through `V36-E`
sequence.

### Closeout / evidence support

- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md`

These do not reopen the locks. They record whether the released slice actually closed
with the promised artifacts, continuity, and evidence.

## The Method In One Sentence

The repo tries to avoid "brief -> prompt -> implementation" as the governing path.

Instead it prefers:

1. name the problem and candidate artifact family;
2. narrow one bounded arc with explicit prohibitions;
3. release typed substrate before rendered behavior;
4. release one bounded reference instance before generalization;
5. release diagnostics and conformance before compiler widening;
6. release exports only after the earlier stages are frozen and hash-bound.

The `ux_morph` family is the cleanest end-to-end example of that sequence.

## Stage 0: The Architectural Thesis

Before the UX family exists, the repo already states the deeper rule:

```text
Canonical JSON + stable hashes + fail-closed validation + explicit evidence.
```

That line appears in `docs/ARCHITECTURE_ADEU_STUDIO_v0.md`.

The semantic-compiler architecture then makes the next move explicit:

```text
"Locked continuation" docs become machine-checkable governance contracts
```

That line appears in `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`.

So the method is not "write docs for humans, then separately write code for machines."
The method is to push docs, schemas, and evidence closer together until the docs can act
as machine-checkable scope surfaces.

## Stage 1: Seed Intent

The seed doc says the object is not generic UI generation:

```text
the real object is not "UI generation."
It is UX governance as a typed ADEU artifact
```

It also gives the artifact ladder early:

```text
ux_domain_packet@1
ux_morph_ir@1
ux_surface_projection@1
ux_interaction_contract@1
ux_morph_diagnostics@1
```

From `docs/seed arc v10.md`, the key shift is:

- frontend work is decomposed into O/E/D/U terms;
- surface law is separated from morphable surface form;
- the first bounded terrain is one ADEU-native family:
  `artifact_inspector_advisory_workbench`.

This matters because the seed is not yet saying "implement page X." It is saying:

- what kind of problem UX is in ADEU terms;
- what artifact families would be needed to make it governable;
- what not to collapse together too early.

That is the first scoping move.

## Stage 2: Planning Turns The Seed Into A Sequence

`docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` takes the seed and turns it into a bounded staged
roadmap:

```text
make surface generation artifact-first rather than prompt-first:
  ux_domain_packet@1 -> ux_morph_ir@1 -> ux_surface_projection@1 ->
  ux_interaction_contract@1 -> ux_morph_diagnostics@1
```

And it fixes the first family:

```text
start on ADEU Studio's native terrain with one bounded
artifact_inspector_advisory_workbench family
```

This is the second scoping move.

Planning does not authorize the implementation yet, but it does establish:

- the sequence of lanes;
- the currently selected family;
- the boundary against generic design-system drift;
- the principle that UI artifacts may express authority but may not mint authority.

In other words, planning decides what the next family is, but not yet what any one arc is
allowed to ship.

## Stage 3: V36-A Locks The Typed Substrate

`docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md` narrows the first arc to substrate only:

```text
this arc is a typed UX-governance artifact baseline only,
the arc must define ux_domain_packet@1 and ux_morph_ir@1
...
no ux_surface_projection@1, ux_interaction_contract@1, rendered route,
diagnostics engine, or surface compiler export is authorized in this arc
```

This is crucial. The repo does not jump from seed to rendered page. It first releases the
artifact substrate that later stages must consume.

The accepted `ux_morph_ir` reference instance makes that visible:

```json
{
  "reference_surface_family": "artifact_inspector_advisory_workbench",
  "reference_instance_id": "artifact_inspector_reference_main",
  "approved_profile_id": "artifact_inspector_reference",
  "schema": "ux_morph_ir@1",
  "morph_axes": {
    "command_posture": "dual_lane",
    "density": "high",
    "information_posture": "evidence_first",
    "interaction_tempo": "expert_fast_path",
    "navigation_mode": "split_pane",
    "salience_posture": "evidence_and_status_prominent",
    "state_exposure": "full_explicit"
  }
}
```

From `apps/api/fixtures/ux_governance/vnext_plus61/ux_morph_ir_artifact_inspector_reference.json`.

The important point is that this is not a style guide. It is a typed constitutional
surface with:

- ontology
- epistemics
- deontics
- utility
- authority boundary policy
- allowed morph axes

The schema itself freezes the vocabulary:

```json
{
  "command_posture": {
    "enum": ["dual_lane", "safe_buffered"]
  },
  "density": {
    "enum": ["high", "medium"]
  },
  "navigation_mode": {
    "enum": ["hub_and_spoke", "split_pane"]
  }
}
```

From `packages/adeu_core_ir/schema/ux_morph_ir.v1.json`.

That is why the substrate matters. The repo is not saying "please make a nice split-pane
expert UI." It is saying "the allowed axis vocabulary is now typed and released."

The v61 closeout doc then proves the arc only shipped that substrate:

```json
{
  "schema": "v36a_ux_domain_morph_ir_evidence@1",
  "reference_instance_binding_verified": true,
  "approved_profile_cardinality_verified": true,
  "no_free_form_ui_codegen_without_ir_preserved": true,
  "ui_artifacts_may_express_but_may_not_mint_authority_preserved": true
}
```

From `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`.

## Stage 4: V36-B Adds Projection And Interaction, But Still No Rendered Surface

The next lock, `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`, still refuses to widen too
early:

```text
this arc is a typed UX-governance projection/interaction artifact baseline only
...
no rendered route, diagnostics engine, conformance report, or surface compiler export
is authorized in this arc
```

What is added here is not pixels. It is the contract that later rendered surfaces must
obey.

The v62 closeout evidence makes the intent concrete:

```json
{
  "schema": "v36b_surface_projection_interaction_evidence@1",
  "projection_interaction_binding_verified": true,
  "reference_profile_id_verified_against_v36a_table": true,
  "authoritative_gate_source_resolution_verified": true,
  "stable_provenance_hooks_verified": true,
  "implementation_observable_bindings_verified": true,
  "evidence_before_commit_rule_preserved": true
}
```

From `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`.

This stage is easy to underestimate if you mostly think in component trees. But it is the
bridge that makes the later UI auditable:

- authority-bearing actions must have explicit source resolution;
- evidence-before-commit must remain preserved;
- provenance hooks and implementation-observable bindings must already exist before the
  rendered route is trusted;
- later diagnostics do not have to infer everything from raw page code.

This is the third scoping move: release the projection law before the rendered surface.

## Stage 5: V36-C Releases One Bounded Rendered Reference Surface

Only after substrate and projection exist does the repo allow one rendered route.

`docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md` keeps this extremely narrow:

```text
this arc authorizes one bounded L0 rendered reference-surface lane plus its closeout
evidence lane only
...
no new L1 diagnostics/conformance release is authorized in this arc
...
no compiler export, variant widening, generic design-system release, or broad route
retrofit is authorized
```

The corresponding closeout evidence describes the rendered route in machine-checkable
terms:

```json
{
  "schema": "v36c_artifact_inspector_reference_surface_evidence@1",
  "rendered_surface_route_path": "/artifact-inspector",
  "epistemic_state_rendering_verified": true,
  "same_context_evidence_visibility_preserved": true,
  "advisory_authoritative_boundary_rendering_verified": true,
  "explicit_commit_or_handoff_boundary_visible": true,
  "stable_provenance_hooks_exposed": true,
  "implementation_observable_bindings_exposed": true
}
```

From `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`.

This is where a frontend specialist can see the repo's method clearly:

- first there is one bounded reference route;
- it is not yet a broad retrofit;
- it is not trusted because it looks good;
- it is trusted because it remains bound to the previously released substrate and
  projection contracts.

The repo's UI implementation for this surface lives in `apps/web`, but the route is not
the source of truth by itself. It is one rendered consequence of the earlier artifact
stack.

## Stage 6: V36-D Makes Diagnostics And Conformance Typed

Once the route exists, the next question is not "can we generate variants?" It is "can we
evaluate the surface deterministically and fail closed?"

That is what `V36-D` adds.

The canonical diagnostics artifact says exactly which violation families are in scope:

```json
{
  "schema": "ux_morph_diagnostics@1",
  "seeded_violation_families": [
    "advisory_authoritative_boundary_visually_collapsed",
    "competing_primary_actions_in_one_region",
    "destructive_action_lacks_adequate_confirmation",
    "failure_mode_lacks_visible_recovery_path",
    "provisional_data_rendered_with_authoritative_styling",
    "requested_interaction_profile_conflicts_with_realized_command_grammar",
    "required_evidence_not_reachable_within_same_bounded_workbench_context",
    "utility_target_conflicts_with_density_or_information_posture"
  ],
  "severity_taxonomy": ["error", "warning", "advisory"]
}
```

From `apps/api/fixtures/ux_governance/vnext_plus64/ux_morph_diagnostics_artifact_inspector_reference.json`.

The corresponding conformance report freezes the aggregation rule:

```json
{
  "schema": "ux_conformance_report@1",
  "derivation_metadata": {
    "aggregation_rule": {
      "any_error": "fail",
      "no_error_and_any_warning": "needs_review",
      "only_advisory_or_no_findings": "pass"
    },
    "canonical_artifact_truth_only": true,
    "event_streams_and_worker_prose_provenance_only": true,
    "fresh_route_local_heuristics_introduced": false
  },
  "overall_judgment": "pass"
}
```

From `apps/api/fixtures/ux_governance/vnext_plus64/ux_conformance_report_artifact_inspector_reference.json`.

And the closeout evidence makes the doctrine explicit:

```json
{
  "schema": "v36d_morph_diagnostics_conformance_evidence@1",
  "diagnostics_severity_taxonomy_verified": true,
  "rendered_surface_assertion_bridge_verified": true,
  "conformance_aggregation_rule_verified": true,
  "no_taste_engine_drift_detected": true,
  "diagnostic_truth_substitution_rejected": true
}
```

From `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md`.

This stage is where the method becomes visibly different from normal frontend process.

Instead of:

- run local heuristics,
- discuss taste,
- approve manually,

the repo tries to say:

- these are the named violation families;
- this is the frozen severity taxonomy;
- this is the conformance aggregation rule;
- this surface may pass, need review, or fail for typed reasons;
- worker prose and event streams are provenance only, not truth substitution.

That is the fourth scoping move: diagnostics before generalization.

## Stage 7: V36-E Allows Compiler Export And Lawful Variants

Only after diagnostics and conformance are released does the repo allow export.

`docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md` says:

```text
this arc is one bounded surface-compiler export and controlled lawful-variant
baseline only
...
exactly two approved profile ids are in scope:
  artifact_inspector_reference and artifact_inspector_alternate
...
implementation exports must remain derived from canonical UX artifacts,
not side-channel prompts, local route heuristics, or free-form brief interpretation
```

The export artifact itself makes that visible:

```json
{
  "approved_profile_id": "artifact_inspector_reference",
  "derivation_metadata": {
    "bounded_css_token_map_only": true,
    "derived_from_canonical_artifacts_only": true,
    "local_route_heuristics_rejected": true,
    "side_channel_prompt_inputs_rejected": true,
    "implementation_target_domains": [
      "react_tree",
      "route_module",
      "state_store_contract",
      "component_binding_map",
      "css_token_map",
      "test_targets"
    ]
  }
}
```

From
`apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_export_artifact_inspector_reference.json`.

The variant manifest then shows the meta-index explicitly by carrying the source-hash set
across all earlier stages:

```json
{
  "schema": "ux_surface_compiler_variant_manifest@1",
  "canonical_profile_designation": "artifact_inspector_reference",
  "alternate_profile_designation": "artifact_inspector_alternate",
  "export_artifact_refs": [
    "apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_export_artifact_inspector_reference.json",
    "apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_export_artifact_inspector_alternate.json"
  ],
  "profile_variants": [
    {
      "approved_profile_id": "artifact_inspector_reference",
      "conformance_gating_result_by_profile": "pass"
    },
    {
      "approved_profile_id": "artifact_inspector_alternate",
      "conformance_gating_result_by_profile": "pass"
    }
  ]
}
```

From
`apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_variant_manifest_artifact_inspector.json`.

The closeout evidence then proves that the export lane closed under the promised guards:

```json
{
  "schema": "v36e_surface_compiler_export_evidence@1",
  "approved_profile_cardinality_verified": true,
  "canonical_export_emitted_and_pass_gated": true,
  "alternate_lawful_export_emitted_and_pass_gated": true,
  "side_channel_prompt_or_local_heuristic_inputs_rejected": true,
  "out_of_table_profile_combinations_rejected": true,
  "no_visual_authority_inflation_preserved": true
}
```

From `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md`.

This is the fifth scoping move:

- first one accepted reference profile;
- then one alternate lawful profile;
- both must stay inside the approved-profile table;
- both must pass the frozen conformance rule;
- both remain traceable to the earlier artifacts and evidence.

The compiler is therefore not a free generator. It is a bounded exporter over previously
accepted law.

## What The Meta-Index Actually Looks Like

Across `V36-A` through `V36-E`, the same identifiers keep reappearing:

- `reference_surface_family`
- `reference_instance_id`
- `approved_profile_id`
- `schema`
- `contract_source`

And the later stages keep recording the earlier stages as consumed-without-drift or
hash-bound predecessors.

That is the practical shape of the meta-index.

It is not one giant master document. It is a linked graph of:

- planning surfaces
- lock contracts
- artifact schemas
- accepted fixtures
- rendered reference surfaces
- diagnostics and conformance artifacts
- export manifests
- stop-gate and closeout evidence

The change is scoped methodically because each stage can only add one bounded layer while
explicitly consuming the earlier ones.

## Why Schema Discipline And The Repo's "Meta-Schema Layer" Matter

It is easy to talk about a "meta-schema" here as if there were one single magical file.
That would be misleading.

In repo terms, the important thing is the schema discipline as a whole:

- lock docs carry machine-checkable JSON blocks;
- released artifact families carry explicit `schema` ids;
- authoritative JSON Schemas live under `packages/.../schema/`;
- mirrored reference schemas live under `spec/`;
- closeout evidence records exact paths, hashes, and continuity relations.

That matters for four reasons.

### 1. It prevents scope drift by prose alone

Without typed contracts, a frontend change can quietly widen:

- what counts as authoritative;
- what counts as same-context evidence;
- what actions are treated as primary;
- what provisional states look final.

With typed contracts, those are named surfaces and checked boundaries.

### 2. It separates "shape exists" from "release is authorized"

Planning can say a future family exists in concept.

Locks then say whether a concrete schema or emitted artifact is authorized in this arc.

Closeout evidence then proves whether the release actually happened.

This separation is one of the repo's central strengths.

### 3. It makes docs indexable by machines instead of only readable by humans

The semantic-compiler architecture exists to push the repo in this direction:

```text
docs -> machine-checkable contracts
```

That makes the documentation layer part of the control plane rather than just a narrative
around the code.

### 4. It keeps the frontend lane from collapsing back into vibes

The UX family demonstrates this directly.

The repo can talk about:

- advisory vs authoritative separation;
- evidence-before-commit;
- morph-axis legality;
- lawful profile variance;
- diagnostics severity and conformance;

without reducing those to vague review taste.

## What A Frontend Specialist Should Notice In This Sequence

If your background is frontend, the important takeaway is not "this repo likes lots of
docs." The important takeaway is:

- the repo treats UX as a governance problem, not only a composition problem;
- surface law is released before surface variation;
- one bounded reference surface closes before lawful variants are exported;
- diagnostics are typed before compiler widening is allowed;
- authority is never supposed to be minted by layout, salience, or copy alone.

That is a much higher bar than ordinary design-system process, but it is also much more
explicit about what the UI is actually allowed to mean.

## Practical Reading Order In The Repo

If someone wants to follow the case directly in-tree, this is the shortest useful path:

1. `docs/seed arc v10.md`
2. `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
3. `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
4. `apps/api/fixtures/ux_governance/vnext_plus61/ux_morph_ir_artifact_inspector_reference.json`
5. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
6. `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
7. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
8. `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
9. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`
10. `apps/web/src/app/artifact-inspector/page.tsx`
11. `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md`
12. `apps/api/fixtures/ux_governance/vnext_plus64/ux_morph_diagnostics_artifact_inspector_reference.json`
13. `apps/api/fixtures/ux_governance/vnext_plus64/ux_conformance_report_artifact_inspector_reference.json`
14. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md`
15. `docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md`
16. `apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_export_artifact_inspector_reference.json`
17. `apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_variant_manifest_artifact_inspector.json`
18. `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md`

## Bottom Line

The `ux_morph` case is a useful introduction because it shows the repo's method on terrain
that a frontend specialist already understands:

- a change is not scoped by a loose brief;
- it is scoped by a chain of typed and linked authority surfaces;
- each arc adds one bounded layer and forbids the rest;
- the rendered UI is one stage in the chain, not the whole source of truth;
- lawful variation comes only after substrate, projection, rendering, and diagnostics are
  already released and evidence-bound.

If someone understands that sequence, they will understand a large part of how this repo
tries to build software in general.
