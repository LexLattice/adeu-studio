# Draft Schema Role-Form Registry v0

Status: working draft companion for the `V45-A` schema-family-registry lane.

Authority posture:

- this document is a planning/decomposition companion;
- it is not a lock doc;
- it does not authorize schema release or implementation by itself;
- it does not settle final role-form doctrine by itself.

Related inputs:

- `docs/DRAFT_SCHEMA_META_CORE_v0.md`
- `docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `docs/DRAFT_SCHEMA_CORPUS_ANALYSIS_GPTPRO_v0.md`

## 1. Purpose

Provide a working doctrine for how `repo_schema_family_registry@1` should classify
schemas by:

- primary carrier role;
- optional secondary role-form tags;
- lineage overlay;
- epistemic posture;
- residual drift posture.

## 2. Direct Answer

Schema role-form classification should not be one flat label guessed from filenames.

The working registry model should instead record:

- a stable core-envelope view;
- one primary carrier overlay;
- optional secondary role-form tags;
- one lineage overlay;
- explicit residual flags where the schema does not cleanly converge.

## 3. Candidate Role-Form Layers

The registry should distinguish several related layers.

It should also keep three distinct row meanings explicit:

- `family_cluster`
  - observational grouping within the bounded corpus view;
- `primary_carrier_class`
  - dominant carrier-role posture for the schema row;
- `lineage_overlay`
  - irreducible anchor, governance, or lineage vocabulary family that persists even
    when carrier form is shared.

These are not interchangeable fields.

### 3.1 Primary carrier class

The primary carrier class should come from the current working overlay set:

- `IntakeFrame`
- `TraceRecord`
- `CuratedSet`
- `Adjudication`
- `ContractGate`
- `StructuralModel`

### 3.2 Secondary role-form tags

Secondary role-form tags should capture the more familiar finer-grained form, such as:

- packet
- frame
- request
- candidate
- trace
- record
- log
- token
- bundle
- manifest
- registry
- catalog
- table
- glossary
- snapshot
- report
- diagnostics
- resolution
- evidence
- result
- explain
- contract
- policy
- ir
- graph
- payload
- delta
- projection
- plan

The registry should allow:

- one primary carrier class;
- zero or more secondary role-form tags;
- one lineage overlay;
- named residual flags.

## 4. Determination Rules

Role-form classification should not remain vibe-based.

The registry should classify schemas using this precedence order:

1. structural signature
   - characteristic required fields
   - object topology
   - reference posture
   - trace vs set vs request vs contract structure
2. semantic function
   - what the schema does in the artifact system when structure alone is insufficient
3. governance role
   - source, derivative, settlement, diagnostic, request, contract, report, trace,
     registry, or similar posture
4. lexical naming
   - filename, schema ID, and naming-family cues only as lower-precedence support

Lexical naming may support classification.

It should not settle classification by itself when stronger evidence disagrees.

## 5. Epistemic Posture And Promotion Law

The registry should make explicit whether a classification is:

- observed
- derived deterministically
- inferred heuristically
- adjudicated
- settled

For `V45-A`, the promotion law should at least make explicit:

- what evidence is required for `inferred -> adjudicated`
- who or what may perform that promotion
- what evidence is required for `adjudicated -> settled`
- which evidence kinds are admissible for each promotion step
- whether `settled` is allowed outside the bounded reconstruction subset
- which fields may remain only inferred in the first bounded release

For the first bounded slice, the safest working rule is:

- `settled` should remain rare;
- `settled` should usually be limited to the representative reconstruction subset or
  rows backed by an explicit adjudication artifact plus policy-bound support;
- accepted `settled` rows should not rely on lexical naming against stronger
  structural or semantic evidence.

This remains a working doctrine for the first slice, not a released constitutional rule.

The emitted registry should also bind to one explicit classification-policy surface via:

- `classification_policy_ref`
- immutable content hash posture for that policy

so the registry never points at interpretive air.

## 6. Candidate Registry Row Shape

Each schema row in the registry should likely carry fields such as:

- `schema_key`
- `schema_path`
- `schema_discriminator`
- `family_cluster`
- `primary_carrier_class`
- `secondary_role_form_tags`
- `lineage_overlay`
- `core_envelope_features`
- `residual_flags`
- `classification_posture`
- `classification_method`
- `supporting_evidence_refs`
- `adjudication_note` when applicable

Supporting evidence should remain typed rather than free-form.

Illustrative admissible evidence kinds for `V45-A` are:

- observed anchor tuple evidence
- structural signature evidence
- semantic function cue evidence
- governance cue evidence
- lexical cue evidence
- adjudication artifact evidence
- reconstruction subset evidence

These names are candidate registry fields, not frozen schema anchors.

## 7. Bounded Benchmark Appendix

This registry doctrine should be forced through one bounded representative subset.

At minimum, the first slice should include examples spanning:

- ARC operational
- architecture analysis
- meta-loop
- UX
- core structural integrity
- policy/runtime
- legacy/open-map residuals

For each case, the appendix should show:

- primary carrier class
- secondary role-form tags
- lineage overlay
- residual flags
- why the precedence order lands there
- how the concrete schema reconstructs from the decomposition

This is the main anti-handwave requirement for `V45-A`.

## 8. Non-Goals

This registry note should not be read as authorization to:

1. force every schema into one perfect carrier class without residuals;
2. erase lineage-specific governance distinctions;
3. treat the current registry vocabulary as final ADEU constitution;
4. widen into mutation or recursive-governance doctrine.

## 9. Machine-Checkable Seed Summary

```json
{
  "schema": "schema_role_form_registry_seed@1",
  "artifact": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
  "artifact_status": "draft",
  "authority_layer": "planning_decomposition_companion",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "target_family": "V45-A_schema_family_registry_lane",
  "primary_carrier_class_required": true,
  "secondary_role_form_tags_allowed": true,
  "lineage_overlay_required": true,
  "residual_flags_required": true,
  "role_form_precedence_required": [
    "structural_signature",
    "semantic_function",
    "governance_role",
    "lexical_naming"
  ],
  "classification_posture_required": [
    "observed",
    "derived_deterministically",
    "inferred_heuristically",
    "adjudicated",
    "settled"
  ],
  "bounded_registry_appendix_required": true,
  "source_docs": [
    "docs/DRAFT_SCHEMA_META_CORE_v0.md",
    "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/DRAFT_SCHEMA_CORPUS_ANALYSIS_GPTPRO_v0.md"
  ]
}
```
