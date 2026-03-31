# Draft Schema Meta Core v0

Status: working draft support/decomposition companion for the `V45-A` schema-family-
registry lane.

Authority posture:

- this document is a support/planning companion;
- it is not a lock doc;
- it does not settle the ADEU schema constitution by itself;
- it does not authorize schema release, implementation, or recursive-governance
  widening by itself.

Related inputs:

- `docs/DRAFT_SCHEMA_CORPUS_ANALYSIS_GPTPRO_v0.md`
- `docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`

## 1. Direct Answer

The current best branch-local hypothesis for the ADEU schema corpus is:

```text
common core envelope
  + carrier overlays
  + lineage overlays
  + narrow named residuals
```

This is a stronger working abstraction than:

- one flat universal field grammar;
- or one fully fragmented family-per-family schema ontology.

It should be treated as a planning-grade hypothesis for `V45-A`, not as a settled ADEU
schema constitution.

## 2. Why This Matters For `V45-A`

`V45-A` needs a schema-family registry that can do more than cluster schemas by
filename.

The schema corpus already shows strong recurring stability around:

- discriminator posture;
- root closure posture;
- anchor posture;
- governance posture;
- lineage/evidence posture;
- settlement or boundedness posture.

The main variation is then better modeled as:

- carrier variation;
- lineage-specific anchor/governance vocabularies;
- narrow residual drift.

That is why the schema corpus is a good first bounded subcorpus for the repo
self-description family.

## 3. Stable Core Envelope

The stable thing is primarily the envelope, not the inner payload.

The current candidate universal envelope is:

- discriminator:
  - `schema`
  - or legacy `schema_version`
- closure/typing posture:
  - closed root object by default
  - local named defs posture
- anchors:
  - ids
  - refs
  - hashes
  - sequence or time anchors
- governance envelope:
  - authority basis/boundary
  - boundedness or scope
  - settlement posture
  - advisory vs authoritative posture
- evidence/lineage envelope:
  - source bindings
  - evidence bindings
  - derivation or compilation provenance

This candidate core should remain explicit about legacy drift rather than pretending the
older strata already conform fully.

## 4. Candidate Carrier Overlays

The current best carrier classes are:

1. `IntakeFrame`
   Subkinds:
   - packet
   - frame
   - request
   - candidate
2. `TraceRecord`
   Subkinds:
   - trace
   - record
   - log
   - token
3. `CuratedSet`
   Subkinds:
   - bundle
   - manifest
   - registry
   - catalog
   - table
   - glossary
   - snapshot
4. `Adjudication`
   Subkinds:
   - report
   - diagnostics
   - resolution
   - evidence
   - result
   - explain
5. `ContractGate`
   Subkinds:
   - contract
   - policy
6. `StructuralModel`
   Subkinds:
   - ir
   - graph
   - payload
   - delta
   - projection
   - plan

These should be treated as current working carrier overlays, not frozen ontology.

## 5. Candidate Lineage Overlays

The current best lineage overlays are:

- `ARCOperational`
- `ArchitectureAnalysis`
- `MetaLoopControl`
- `UXSurface`
- `SyntheticPressureMismatch`
- `PolicyRuntime`
- `CoreStructuralIntegrity`
- `LegacyIRValidator`

These overlays exist because anchor vocabularies and governance vocabularies do not
fully collapse into one carrier-only classification.

## 6. Residuals And Drift

The current best model still requires explicit named residuals.

Important residual classes include:

- legacy discriminator drift:
  - `schema_version`
  - or neither `schema` nor `schema_version`
- narrow named open maps:
  - `metadata`
  - `details`
  - `options`
  - `semantic_policy_json`
  - `proposed_action_payload`
- microform or singleton awkward cases:
  - `policy_activation_log`
  - `scheduler_dispatch_token`
  - `connector_snapshot`
- legacy/open-map validator and puzzle strata

Residuals should remain explicit, narrow, and named.

They should not be hidden under one generic "misc" escape hatch.

## 7. Bounded Reconstruction Requirement

This hypothesis is not strong enough on prose alone.

Before it should shape any later lock surface, `V45-A` should require one bounded
representative subset where each concrete schema is decomposed into:

- core envelope fields;
- carrier overlay;
- lineage overlay;
- residuals;

and then reconstructed back to the concrete schema definition explicitly.

Illustrative bounded subset:

- `adeu_arc_task_packet`
- `adeu_architecture_analysis_request`
- `meta_loop_sequence_contract`
- `ux_interaction_contract`
- `adeu_core_ir`
- `policy_registry`
- `adeu.validator_result`

The goal is not grand theory first.

The goal is an auditable schema-registry kernel for `V45-A`.

## 8. Non-Goals

This draft should not be read as authorization to:

1. flatten the entire schema corpus into one lock-level meta-schema now;
2. erase carrier distinctions or lineage-specific governance distinctions;
3. widen directly into Lean-first formalization work;
4. widen into recursive amendment or mutation doctrine;
5. treat the current carrier/lineage overlay vocabulary as constitutionally settled.

## 9. Machine-Checkable Seed Summary

```json
{
  "schema": "schema_meta_core_seed@1",
  "artifact": "docs/DRAFT_SCHEMA_META_CORE_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_companion",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "target_family": "V45-A_schema_family_registry_lane",
  "current_best_hypothesis": "common_core_plus_carrier_overlays_plus_lineage_overlays_plus_narrow_residuals",
  "stable_envelope_priority_required": true,
  "carrier_overlay_model_required": true,
  "lineage_overlay_model_required": true,
  "named_residuals_required": true,
  "bounded_reconstruction_subset_required": true,
  "hypothesis_not_yet_settled_constitution": true,
  "source_docs": [
    "docs/DRAFT_SCHEMA_CORPUS_ANALYSIS_GPTPRO_v0.md",
    "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
  ]
}
```
