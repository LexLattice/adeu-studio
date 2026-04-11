I inspected the repo-native doctrine and schema families most relevant to this question: `docs/DRAFT_SCHEMA_META_CORE_v0.md`, `docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md`, `docs/DRAFT_SCHEMA_CORPUS_ANALYSIS_GPTPRO_v0.md`, `docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md`, `AGENTS.md`, `README.md`, `REPO_ATLAS.md`, the UX lineage in `packages/adeu_core_ir/schema/ux_*` plus `packages/adeu_core_ir/src/adeu_core_ir/ux_governance.py`, the architecture lineage in `packages/adeu_architecture_ir/schema/*` and `packages/adeu_architecture_compiler/schema/*`, the meta-loop lineage in `packages/adeu_core_ir/schema/meta_loop_*`, and the repo-description registries in `packages/adeu_repo_description/schema/*` plus their validators. Across `packages/*/schema/*.json`, the corpus currently has 155 schema files; all 155 are closed-root (`additionalProperties: false`), 147 expose a `schema` discriminator, and only 15 require it, which confirms both a strong shared envelope and explicit legacy drift.

The repo-native answer is not “one universal ADEU blob schema.” The recurring structure is:

**core envelope + carrier overlay + lineage overlay + family contract + project-type grammar + instance realization + explicit residuals**

That is the higher-order grammar that should govern future concrete ADEU schema families.

What follows is a **repo-native working canonical meta-grammar**. It is canonical in the sense that it best fits the current corpus and validators. It is not a claim that every part is already lock-settled, because several of the doctrine documents explicitly mark themselves as planning/support artifacts.

---

# 1. ADEU_SCHEMA_META_GRAMMAR

## 1.1 Direct derivation

The strongest direct statement already exists in `docs/DRAFT_SCHEMA_META_CORE_v0.md` and `docs/DRAFT_SCHEMA_CORPUS_ANALYSIS_GPTPRO_v0.md`: the corpus is best explained by a **common core envelope**, plus **carrier overlays**, plus **lineage overlays**, plus **narrow named residuals**.

The missing step is to lift that from corpus-description into **schema-authoring doctrine**.

The resulting meta-grammar is:

```text
ADEU concrete family authoring grammar

Family =
  MetaEnvelopeContract
  + FamilyContract
  + ProjectTypeContract
  + InstanceRealizationContract

Artifact within family =
  ArtifactCoreEnvelope
  + PrimaryCarrierOverlay
  + PrimaryLineageOverlay
  + FamilyLocalPayload
  + NamedResiduals?
```

The decisive repo-native insight is that **constitutional sameness lives in slot-classes, not in identical field names**.

For example:

* UX realizes authority via `UXAuthorityBoundaryPolicy` in `ux_governance.py`.
* Architecture realizes authority via its own policy object in `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`.
* Repo-description realizes promotion/authority separation in `repo_descriptive_normative_binding_frame.v1.json`.

These are not the same payload, but they are the same **constitutional slot**: an explicit authority-boundary surface.

## 1.2 Constitutional slot classes

A new ADEU family should be considered born-aligned only if it realizes these slot classes.

### A. Discriminator and closure posture

The corpus shows near-universal discriminator posture and fully universal closed-root posture.

So for new families:

* `schema` should be the preferred discriminator and should be required.
* root objects should be closed by default.
* any openness must appear as a narrow, explicitly named residual, never as a hidden generic escape hatch.

This is exactly the pattern described in `DRAFT_SCHEMA_META_CORE_v0.md`: legacy drift is tolerated, not normalized.

### B. Anchor posture

A family must realize anchor slots for at least some combination of:

* identity anchors,
* reference anchors,
* hash anchors,
* sequence/time or snapshot anchors,
* supporting-artifact anchors.

This is visible everywhere, but with different family-local names:

* UX: `reference_instance_id`, `reference_surface_family`, `approved_profile_id`, `supporting_artifacts`
* Architecture: `intent_packet_id`, `architecture_id`, `semantic_hash`, `variant_lineage`
* Repo-description: `repo_snapshot_id`, `repo_snapshot_hash`, `classification_policy_ref`, `classification_policy_hash`

The meta-level law is not “use these exact names.” It is “do not author a family without explicit anchors.”

### C. Governance posture

A family must realize explicit governance slots for:

* authority boundary,
* bounded scope or impact posture,
* advisory vs authoritative distinction,
* settlement or promotion posture where applicable.

This is not optional. It is one of the strongest recurring corpus signals.

### D. Evidence / lineage / derivation posture

A family must realize explicit slots for:

* source bindings,
* evidence bindings,
* derivation / compilation provenance,
* authoritative aggregation or adjudication basis where it issues reports.

This is supported by `repo_schema_family_registry.v1.json`, the UX diagnostics/conformance pair, the architecture checkpoint/conformance surfaces, and the repo-wide “canonical JSON + stable hashes + fail-closed validation + explicit evidence” spine noted in `REPO_ATLAS.md`.

### E. Semantic frame requirement

A family must declare how it expresses the ADEU frame:

* Ontology
* Epistemics
* Deontics
* Utility

Not every artifact needs these as top-level sibling fields. But the family contract must say where they live.

This is already explicit in:

* `ux_morph_ir@1`: `ontology`, `epistemics`, `deontics`, `utility`
* `adeu_architecture_semantic_ir@1`: `ontology`, `epistemics`, `deontics`, `utility`
* `README.md`, which names O/E/D/U as the repo frame

So the meta-law is: **every new family must declare its O/E/D/U realization strategy**.

## 1.3 Carrier overlays

`DRAFT_SCHEMA_META_CORE_v0.md`, `DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md`, and the repo schema-family registry converge on six working carrier classes:

* `IntakeFrame`
* `TraceRecord`
* `CuratedSet`
* `Adjudication`
* `ContractGate`
* `StructuralModel`

The key authoring rule is:

**carrier is per-artifact, not per-family**

A family is usually a ladder of artifacts spanning several carriers.

This is one reason flattening everything into one generic family blob is wrong.

## 1.4 Lineage overlays

The observed lineages currently include:

* `ARCOperational`
* `ArchitectureAnalysis`
* `MetaLoopControl`
* `UXSurface`
* `SyntheticPressureMismatch`
* `PolicyRuntime`
* `CoreStructuralIntegrity`
* `LegacyIRValidator`

The key authoring rule is:

**lineage overlay is not the same thing as carrier class**

That separation is strongly enforced by `repo_schema_family_registry` validators, which require `family_cluster`, `primary_carrier_class`, and `lineage_overlay` to remain non-equivalent.

## 1.5 Family contract as the missing first-class object

The repo already behaves as if families have contracts, but those contracts are currently distributed across docs, schemas, validators, fixtures, and governance code.

Examples:

* UX family contract is spread across `ux_governance.py`, `ux_*` schemas, and v61-v65 fixtures.
* Architecture family contract is spread across `ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md` and the architecture schemas.
* Meta-loop family contract is spread across `meta_loop_*` schemas.

The missing unifier is a first-class **family contract artifact**.

That family contract should declare:

* the family’s primary lineage overlay,
* its artifact ladder,
* its family-local authority policy,
* its shared binding fields,
* its O/E/D/U realization,
* its diagnostics and conformance rules,
* its deferred seams and residual posture.

That is the core move that makes later concrete families emerge aligned instead of being harmonized afterward.

## 1.6 Concrete authoring grammar

A family should therefore be authored under the following meta pattern:

```text
1. MetaEnvelopeContract
   - discriminator posture
   - closure posture
   - anchor posture
   - governance posture
   - evidence / derivation posture
   - O/E/D/U realization declaration

2. FamilyContract
   - primary lineage overlay
   - artifact ladder
   - shared authority boundary policy
   - shared binding contract
   - diagnostics / conformance contract
   - residual and deferred seam policy

3. ProjectTypeContract
   - family-local ontology
   - project-type grammar
   - task or operating modes
   - invariants and mutation laws
   - family-local evaluation criteria

4. InstanceRealizationContract
   - actual reference ids / hashes / source refs
   - approved profiles / variants
   - diagnostics and conformance outputs
   - export / manifest bindings
```

---

# 2. ADEU_SCHEMA_LAYER_MODEL

The cleanest layer model is four-layered, with a descriptive/normative split running across it.

## Layer 0 — Meta-schema / constitutional slot layer

This layer governs what every future family must realize in some form.

It defines:

* slot classes,
* overlay vocabulary,
* classification precedence,
* authority and evidence laws,
* residual posture,
* settlement/promotion posture.

It does **not** define family-local surface vocabulary such as `transcript_lane`, `world_hypothesis`, or `checkpoint_entry`.

Those belong lower.

## Layer 1 — Family contract layer

This layer governs one schema family.

It defines:

* which lineage overlay the family belongs to,
* which artifacts make up the family ladder,
* which carrier class each artifact uses,
* shared authority policy,
* shared cross-artifact bindings,
* family-local O/E/D/U structure,
* diagnostics and conformance rules,
* export and variant behavior if the family emits downstream artifacts.

Examples already visible in the repo:

* UXSurface family
* ArchitectureAnalysis family
* MetaLoopControl family

## Layer 2 — Concrete project-type grammar layer

This layer governs the semantics of one concrete project type inside a family.

This is where things like these belong:

* the semantic role of transcript vs composer vs runtime vs diff,
* invariant vs semi-stable vs morphable distinctions,
* task/mode packets,
* user cognitive packet models,
* lawful operations,
* forbidden semantic laundering operations,
* fit evaluation criteria.

This is the layer where your prior `AGENTIC_DE_TYPE_GRAMMAR` belongs.

It is not meta-level. It is a concrete project-type contract.

## Layer 3 — Instance realization layer

This layer governs actual bound instances.

It includes:

* actual `reference_instance_id`-style bindings,
* approved profile IDs,
* source set and hashes,
* supporting artifact refs,
* authoritative gate sources,
* emitted diagnostics,
* conformance outputs,
* export artifact refs,
* variant manifests.

The UX fixtures make this explicit: the family is not complete at the abstract grammar level until there is a reference instance and profile-bound realization.

## Cross-cutting descriptive vs normative split

Following `DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md` and `repo_descriptive_normative_binding_frame.v1.json`, every layer must also distinguish:

* descriptive artifacts, which classify, report, or constrain,
* normative/contract artifacts, which govern allowed behavior.

Descriptive artifacts may constrain interpretation.
They may not mint authority by themselves.

That rule matters later for fit diagnostics, registry classifications, and agent-driven adaptation reports.

---

# 3. ADEU_SCHEMA_AUTHORING_PROTOCOL

Future schema families should be authored under a fixed protocol. The protocol should be treated as mandatory scaffolding, not optional cleanup.

## Step 1 — State authority layer and bounded scope

Before field design, the author must declare:

* authority layer: `lock`, `architecture`, `planning`, or `support`
* bounded scope
* non-goals
* settlement posture
* whether the artifact is descriptive, normative, or hybrid

This follows `AGENTS.md` and the repo’s horizon-sensitive doctrine.

## Step 2 — Separate descriptive basis from normative intent

Authors must distinguish:

* what was observed from repo reality, domain reality, or accepted inputs,
* what is newly normative,
* what remains advisory,
* what is still hypothetical or deferred.

This prevents silent promotion from analysis into authority.

## Step 3 — Choose lineage overlay

The author must select the best-fit primary lineage overlay.

That choice should be justified by:

1. structural signature
2. semantic function
3. governance role
4. lexical naming only last

This directly follows `DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md` and `repo_schema_family_registry` validation.

## Step 4 — Define the family contract before payload schemas

The author must first define:

* family ID
* primary lineage overlay
* artifact ladder
* shared authority boundary policy
* shared binding contract
* diagnostics/conformance contract
* deferred seam policy

Only after that should the family-local payload schemas be authored.

This is the central alignment move.

## Step 5 — Define the canonical semantic artifact

Every family that projects outward should have one canonical semantic artifact sitting upstream of projections.

UX already enforces “no free-form UI codegen without IR.”
Architecture already enforces “no direct brief-to-codegen.”

The meta-level generalization is:

**no downstream projection, export, or effectful implementation surface should be authoritative unless a canonical family semantic artifact exists first**

## Step 6 — Define O/E/D/U realization explicitly

The family contract must state where these live:

* ontology
* epistemics
* deontics
* utility

This can be spread across multiple artifacts, but it cannot be left tacit.

## Step 7 — Define cross-artifact bindings and identity law

The family must freeze:

* which IDs recur across artifacts,
* which hashes are authoritative,
* which refs bind to support artifacts,
* which equality constraints hold across artifacts,
* what counts as canonical normalized semantic equivalence for reconstruction.

This is what makes later registry, diagnostics, and compiler exports auditable.

## Step 8 — Define diagnostics and conformance as separate artifacts

Families should not jump directly from semantic IR to “pass/fail.”

They should define at least:

* findings or diagnostics artifact
* conformance or readiness artifact
* aggregation rule or adjudication basis

This separation is explicit in UX and architecture families.

## Step 9 — Define projection/export/variant artifacts if the family emits downstream forms

If the family drives a compiler, projection, or surface emitter, it must define:

* export artifact
* manifest or bundle
* source artifact refs
* gating snapshot or conformance ref
* compiler/version provenance
* variant manifest if multiple lawful variants exist

## Step 10 — Declare residuals and deferred seams

Every gap must be classified, not hidden.

Use the repo-native seam postures from `AGENTS.md`:

* `instantiated_here`
* `deferred_to_later_family`
* `superseded_by_alternate_surface`
* `not_selected_yet`

This should be first-class authoring doctrine, not just review commentary.

## Step 11 — Register the family with typed evidence

Before a family is treated as repo-native, it should be registerable in the schema family registry with:

* structural signature evidence
* semantic function cue evidence
* governance cue evidence
* lexical cue evidence if relevant
* adjudication artifact evidence if settlement is claimed
* bounded reconstruction subset evidence

## Step 12 — Emit reference fixtures and fail-closed validators

A family is not complete until it has at least one reference realization or equivalent bounded fixture set and validator coverage that enforces the family contract.

That is how the repo’s current strongest families gained shape.

---

# 4. ADEU_SCHEMA_ALIGNMENT_LAWS

These are the laws future families should satisfy.

## 1. Envelope-before-payload law

No family-local payload should exist without a declared discriminator posture, closure posture, anchor posture, governance posture, and evidence/derivation posture.

## 2. Closed-root with named residuals law

Root openness is forbidden by default. Any open region must be narrow, explicit, and named.

## 3. Carrier-lineage distinction law

Carrier class and lineage overlay are different axes. They must not collapse into one label.

## 4. Classification precedence law

Structural signature outranks semantic function, semantic function outranks governance-role cues, and lexical naming comes last.

## 5. Authority non-minting law

Projections, UI arrangements, descriptive registries, diagnostics, and reports may express or constrain. They may not mint authority by themselves.

This is visible in:

* `ux_governance.py`
* architecture authority policy
* `repo_descriptive_normative_binding_frame.v1.json`

## 6. Advisory-authoritative separation law

Advisory, candidate, provisional, request-only, applied, and authoritative states must remain distinguishable in schema and projection.

## 7. Canonical-IR-before-projection law

No direct brief-to-codegen and no free-form projection without canonical IR. This is already a family-local law in both UX and architecture. It should become a meta-law for future families that project outward.

## 8. Source-evidence-derivation explicitness law

Every authoritative or adjudicative artifact must bind its source set, evidence basis, and derivation or compilation metadata.

## 9. Deterministic authoritative aggregation law

If a family emits authoritative conformance or readiness judgments, the aggregation rule and authoritative basis must be explicit and non-opaque.

## 10. Bounded settlement law

`settled` posture is rare, requires explicit policy and evidence, and should remain bounded rather than ambient.

This is enforced in the repo-schema-family-registry validators.

## 11. Instance-binding coherence law

Shared IDs, policy refs, profile refs, source refs, and supporting refs must agree across a family’s artifacts. Cross-artifact drift is a schema violation, not a stylistic issue.

## 12. Reconstruction equivalence law

A family’s decomposition and reconstruction should be auditable under canonical normalized semantic equivalence, not vague prose similarity.

## 13. Deferred seam explicitness law

Unselected or future seams must be named and classified, not smuggled in as ambiguity.

## 14. No semantic laundering law

A projection change, family refactor, or new schema may not erase authority boundaries, settlement posture, evidence obligations, or handoff semantics under the cover of re-rendering.

This is the higher-order law that connects your prior morphic-UX thesis to the repo’s existing doctrine.

---

# 5. AGENTIC_DE_REFACTORED_UNDER_META_GRAMMAR

## 5.1 Correct layer placement of the prior work

Your prior bundle was strong, but mostly at **Layer 2**.

That means it was not wrong. It was **mislayered** relative to repo-native family authoring.

Here is the proper placement:

* `AGENTIC_DE_TYPE_GRAMMAR`
  → Layer 2, concrete project-type grammar
  → best future home: `agentic_de_morph_ir@1` or `agentic_de_semantic_ir@1`

* `USER_COGNITIVE_PROFILE_TAXONOMY`
  → Layer 2 payload, possibly with Layer 1 support-curated-set backing
  → best future home: `agentic_de_cognitive_profile_table@1` or domain-packet support

* `TASK_MODE_PROFILE_SCHEMA`
  → Layer 2 payload, possibly with Layer 1 support-curated-set backing
  → best future home: `agentic_de_task_mode_registry@1`

* `MORPHIC_UX_LAW_FOR_AGENTIC_DE`
  → split between Layer 1 family deontics and Layer 2 project-type morph law
  → best future home: family authority policy + `agentic_de_interaction_contract@1` + invariants in semantic IR

* `UX_PROFILE_FAMILY_FOR_AGENTIC_DE`
  → Layer 1 curated-set support artifact
  → best future home: `agentic_de_approved_profile_table@1`

* `PROJECTION_FIT_CRITERIA`
  → Layer 1 diagnostics/conformance contract plus Layer 2 evaluation payload
  → best future home: `agentic_de_morph_diagnostics@1` and `agentic_de_conformance_report@1`

* `RESIDENT_AGENT_MORPHIC_NEGOTIATION_MODEL`
  → Layer 2 semantics plus Layer 1 interaction/deontic constraints
  → best future home: semantic IR + interaction contract + diagnostics

## 5.2 Best current lineage fit

Under the current corpus, the strongest fit is:

**primary lineage overlay: `UXSurface`**

Why:

* the agentic-DE work is fundamentally about lawful surface projection,
* the older morphic-UX family already provides the closest precedent,
* the decisive laws are about projection, authority rendering, evidence adjacency, and interaction contracts.

This should remain a **working classification**, not an unreviewable final settlement. If later authoring shows irreducible anchor/governance vocabulary beyond the current UXSurface lineage, that could justify a new lineage overlay. But the current repo-native fit is UXSurface.

## 5.3 Proposed repo-native family shape

The refactored family should not start as one giant “agentic DE schema.” It should start as a family ladder.

A strong repo-native candidate is:

1. `agentic_de_domain_packet@1`
   IntakeFrame
   Captures user/task/risk/environment/scope packet and supporting tables/glossaries.

2. `agentic_de_morph_ir@1`
   StructuralModel
   Canonical project-type semantic artifact containing ontology, epistemics, deontics, utility, invariants, morph axes, and stable semantic component family.

3. `agentic_de_surface_projection@1`
   StructuralModel / projection
   Materializes regions, zones, anchors, evidence placement, boundary rendering, and cross-morphic continuity structures.

4. `agentic_de_interaction_contract@1`
   ContractGate
   Defines action semantics, gates, authoritative/advisory distinctions, handoff boundaries, runtime-visible consequences.

5. `agentic_de_morph_diagnostics@1`
   Adjudication / diagnostics
   Emits typed findings against projection, anchor, authority, evidence, and fit laws.

6. `agentic_de_conformance_report@1`
   Adjudication / report
   Emits lawful summary judgment using an explicit aggregation rule.

7. `agentic_de_surface_compiler_export@1`
   export artifact
   Binds emitted implementation payloads or reference-surface payloads back to source artifacts and gating snapshots.

8. `agentic_de_surface_compiler_variant_manifest@1`
   CuratedSet / manifest
   Binds lawful variants and approved profiles.

Support artifacts should likely also exist:

* `agentic_de_approved_profile_table@1`
* `agentic_de_task_mode_registry@1`
* `agentic_de_cognitive_profile_table@1`
* `agentic_de_anchor_glossary@1`
* possibly `agentic_de_same_context_reachability_glossary@1`

That shape is much more repo-native than a single free-floating project grammar.

## 5.4 Candidate family-local authority boundary policy

A family-local authority policy for this future family should look more like this:

```json
{
  "no_free_form_surface_or_codegen_without_canonical_ir": true,
  "surface_artifacts_may_express_but_may_not_mint_authority": true,
  "resident_agent_outputs_advisory_until_governed_gate": true,
  "no_hidden_write_execute_or_dispatch_boundary": true,
  "fail_closed_on_unbound_high_risk_evidence": true,
  "layout_morphism_may_not_rewrite_semantic_law": true
}
```

This is the correct repo-native elevation of your prior “morphism must not rewrite semantic law” thesis.

## 5.5 What already aligns well

The prior `AGENTIC_DE_TYPE_GRAMMAR` already aligns strongly in these ways:

* It treats UX as downstream projection rather than upstream law.
* It sharply distinguishes invariant, semi-stable, and morphable.
* It treats authority, evidence, and handoff as semantic distinctions.
* It explicitly guards against semantic laundering.
* It models task mode separately from user cognitive profile.
* It understands the resident agent as a lawful negotiator, not a stylist.
* It already thinks in O/E/D/U terms, even when not always named that way.

Those are genuine repo-native strengths.

## 5.6 What is missing for repo-native fit

To become repo-native under the observed meta-grammar, the prior bundle still lacks:

* a declared family contract,
* explicit lineage overlay selection,
* per-artifact carrier classification,
* shared authority boundary policy object,
* source/evidence/derivation bindings,
* shared cross-artifact reference anchors,
* canonical semantic artifact vs projection vs interaction vs diagnostics separation,
* conformance report with explicit aggregation basis,
* compiler/export and variant-manifest surfaces,
* residual/deferred seam policy,
* registry-ready classification evidence,
* reference fixtures and fail-closed validators.

These are not decorative wrappers. They are the things that make the family auditable and governable.

## 5.7 What is overconcrete

Several parts of the prior answer are overconcrete only if mistaken for meta-level or family-contract fields.

They are **correct project-type content**, but should not be promoted upward:

* `transcript / conversation lane`
* `composer / command entry`
* `project/workspace context`
* `diff / provenance surfaces`
* `terminal / runtime surfaces`
* all concrete task-mode names
* all concrete cognitive dimension names
* all exact UX profile names

These belong inside the project-type grammar and support tables, not in the ADEU meta-schema itself.

Likewise, laws such as spatial anchor preservation, cross-state invariance, and handoff-boundary visibility are excellent project-type instantiations of broader ADEU alignment laws. They should be represented as family-local law realizations, not mistaken for the universal law vocabulary itself.

## 5.8 What should be refactored

The clean refactor is:

* lift the prior work into a **project-type semantic artifact**
* wrap it in a **family contract**
* split projections, contracts, diagnostics, and conformance into separate artifacts
* add shared authority/evidence/derivation bindings
* add support tables/glossaries/approved-profile artifacts
* add a reference instance and profile-bound fixtures
* register the family with typed classification evidence

That is how the prior work becomes repo-native rather than remaining a strong but free-standing theory document.

---

# 6. ADEU_SCHEMA_DIAGNOSTICS_AND_GAP_REPORT

## Overall assessment

The prior `AGENTIC_DE_TYPE_GRAMMAR` is:

**strong as concrete project-type semantics**
**weak as a repo-native family contract**
**not yet a meta-schema**

In other words: **semantically good, structurally incomplete**.

## High-severity gaps

These are the blockers to repo-native adoption as a family:

1. No first-class family contract.
2. No explicit lineage overlay selection and artifact ladder.
3. No shared authority boundary policy object.
4. No explicit source/evidence/derivation envelope.
5. No diagnostics/conformance artifact separation.
6. No instance-binding and export/variant surfaces.

## Medium-severity gaps

These are non-blocking conceptually, but important for alignment:

1. No residual/deferred seam register.
2. No registry-ready classification evidence.
3. No canonical reconstruction/audit story.
4. No declared support tables/glossaries for profiles, tasks, anchors.

## Low-severity gaps

These are refinement issues:

1. Some field names should be normalized to repo-native naming posture.
2. Some evaluation payloads should move from prose into diagnostics/conformance artifacts.
3. Some project-type laws should be recast as family-local realizations of broader alignment laws.

## Positive findings

The prior work already demonstrates:

* strong project-type ontology,
* strong deontic discipline,
* strong evidence and authority modeling,
* strong morph-law discipline,
* strong user/task separation,
* strong anti-laundering posture.

So the right next move is not rewrite-from-scratch.
It is **layer-correct refactoring**.

## Minimum viable refactor set

A future implementation should at minimum author:

* a family contract,
* a canonical semantic artifact,
* an interaction contract,
* diagnostics and conformance artifacts,
* a reference instance fixture,
* registry evidence,
* explicit authority and evidence bindings.

That would be enough to make future concrete project types—agentic DE, text processor, paint workbench, theorem workbench—start from the same authoring grammar.

---

# Machine-checkable schema blocks

These are authoring-level schemas for the meta-grammar itself.

## `adeu_schema_meta_grammar@1`

```json
{
  "$id": "adeu_schema_meta_grammar@1",
  "type": "object",
  "required": [
    "discriminator_posture",
    "closure_posture",
    "constitutional_slot_classes",
    "semantic_frame_requirement",
    "carrier_overlay_system",
    "lineage_overlay_system",
    "classification_precedence",
    "alignment_laws",
    "new_family_minimum_outputs"
  ],
  "properties": {
    "discriminator_posture": {
      "type": "object",
      "required": ["preferred_field", "legacy_fields_allowed", "required_for_new_families"],
      "properties": {
        "preferred_field": { "const": "schema" },
        "legacy_fields_allowed": {
          "type": "array",
          "items": { "enum": ["schema_version"] },
          "uniqueItems": true
        },
        "required_for_new_families": { "const": true }
      },
      "additionalProperties": false
    },
    "closure_posture": {
      "type": "object",
      "required": ["closed_root_required", "named_residuals_only"],
      "properties": {
        "closed_root_required": { "const": true },
        "named_residuals_only": { "const": true }
      },
      "additionalProperties": false
    },
    "constitutional_slot_classes": {
      "type": "array",
      "items": {
        "enum": [
          "identity_anchor",
          "reference_anchor",
          "hash_anchor",
          "sequence_or_snapshot_anchor",
          "authority_boundary",
          "bounded_scope",
          "advisory_authoritative_posture",
          "settlement_or_promotion_posture",
          "source_binding",
          "evidence_binding",
          "derivation_or_compilation_binding",
          "diagnostics_binding",
          "conformance_binding",
          "residual_and_deferred_seam_binding"
        ]
      },
      "uniqueItems": true
    },
    "semantic_frame_requirement": {
      "type": "object",
      "required": ["family_must_declare_representation_for"],
      "properties": {
        "family_must_declare_representation_for": {
          "type": "array",
          "items": {
            "enum": ["ontology", "epistemics", "deontics", "utility"]
          },
          "uniqueItems": true
        }
      },
      "additionalProperties": false
    },
    "carrier_overlay_system": {
      "type": "object",
      "required": ["primary_classes", "single_primary_carrier_per_artifact"],
      "properties": {
        "primary_classes": {
          "type": "array",
          "items": {
            "enum": [
              "IntakeFrame",
              "TraceRecord",
              "CuratedSet",
              "Adjudication",
              "ContractGate",
              "StructuralModel"
            ]
          },
          "uniqueItems": true
        },
        "single_primary_carrier_per_artifact": { "const": true }
      },
      "additionalProperties": false
    },
    "lineage_overlay_system": {
      "type": "object",
      "required": ["known_primary_overlays", "primary_lineage_overlay_required_per_family"],
      "properties": {
        "known_primary_overlays": {
          "type": "array",
          "items": {
            "enum": [
              "ARCOperational",
              "ArchitectureAnalysis",
              "MetaLoopControl",
              "UXSurface",
              "SyntheticPressureMismatch",
              "PolicyRuntime",
              "CoreStructuralIntegrity",
              "LegacyIRValidator",
              "new_lineage_candidate"
            ]
          },
          "uniqueItems": true
        },
        "primary_lineage_overlay_required_per_family": { "const": true }
      },
      "additionalProperties": false
    },
    "classification_precedence": {
      "type": "array",
      "items": {
        "enum": [
          "structural_signature",
          "semantic_function",
          "governance_role",
          "lexical_naming"
        ]
      },
      "minItems": 4,
      "maxItems": 4,
      "uniqueItems": true
    },
    "alignment_laws": {
      "type": "array",
      "items": {
        "enum": [
          "envelope_before_payload",
          "closed_root_named_residuals",
          "carrier_lineage_distinction",
          "authority_non_minting",
          "advisory_authoritative_separation",
          "canonical_ir_before_projection",
          "source_evidence_derivation_explicitness",
          "bounded_settlement",
          "reconstruction_equivalence",
          "instance_binding_coherence",
          "deferred_seam_explicitness",
          "no_semantic_laundering"
        ]
      },
      "uniqueItems": true
    },
    "new_family_minimum_outputs": {
      "type": "array",
      "items": {
        "enum": [
          "family_contract",
          "canonical_semantic_artifact",
          "diagnostics_or_conformance_artifact",
          "reference_fixture_or_instance",
          "validator_tests",
          "registry_classification_evidence"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

## `adeu_schema_family_contract@1`

```json
{
  "$id": "adeu_schema_family_contract@1",
  "type": "object",
  "required": [
    "family_id",
    "authority_layer",
    "family_scope_posture",
    "primary_lineage_overlay",
    "artifact_ladder",
    "family_semantic_frame",
    "authority_boundary_policy_contract",
    "binding_contract",
    "diagnostic_contract",
    "deferred_seam_policy"
  ],
  "properties": {
    "family_id": { "type": "string", "minLength": 1 },
    "authority_layer": {
      "enum": ["lock", "architecture", "planning", "support"]
    },
    "family_scope_posture": {
      "enum": ["candidate", "bounded_release", "released"]
    },
    "primary_lineage_overlay": {
      "enum": [
        "ARCOperational",
        "ArchitectureAnalysis",
        "MetaLoopControl",
        "UXSurface",
        "SyntheticPressureMismatch",
        "PolicyRuntime",
        "CoreStructuralIntegrity",
        "LegacyIRValidator",
        "new_lineage_candidate"
      ]
    },
    "artifact_ladder": {
      "type": "array",
      "minItems": 1,
      "items": {
        "type": "object",
        "required": [
          "artifact_key",
          "primary_carrier_class",
          "secondary_role_form_tags",
          "semantic_role",
          "authoritativeness",
          "required_bindings"
        ],
        "properties": {
          "artifact_key": { "type": "string", "minLength": 1 },
          "primary_carrier_class": {
            "enum": [
              "IntakeFrame",
              "TraceRecord",
              "CuratedSet",
              "Adjudication",
              "ContractGate",
              "StructuralModel"
            ]
          },
          "secondary_role_form_tags": {
            "type": "array",
            "items": {
              "enum": [
                "packet",
                "frame",
                "request",
                "candidate",
                "trace",
                "record",
                "log",
                "token",
                "bundle",
                "manifest",
                "registry",
                "catalog",
                "table",
                "glossary",
                "snapshot",
                "report",
                "diagnostics",
                "resolution",
                "evidence",
                "result",
                "explain",
                "contract",
                "policy",
                "ir",
                "graph",
                "payload",
                "delta",
                "projection",
                "plan"
              ]
            },
            "uniqueItems": true
          },
          "semantic_role": {
            "enum": [
              "intake",
              "semantic_ir",
              "projection",
              "interaction_contract",
              "trace",
              "diagnostics",
              "conformance",
              "export",
              "variant_manifest",
              "supporting_set"
            ]
          },
          "authoritativeness": {
            "enum": [
              "advisory_only",
              "descriptive_only",
              "governance_bound",
              "derived_authoritative"
            ]
          },
          "required_bindings": {
            "type": "array",
            "items": {
              "enum": [
                "schema_discriminator",
                "identity_anchor",
                "reference_anchor",
                "hash_anchor",
                "source_binding",
                "evidence_binding",
                "authority_boundary_policy",
                "supporting_artifact_refs",
                "conformance_ref",
                "diagnostics_ref"
              ]
            },
            "uniqueItems": true
          }
        },
        "additionalProperties": false
      }
    },
    "family_semantic_frame": {
      "type": "object",
      "required": ["ontology_surface", "epistemics_surface", "deontics_surface", "utility_surface"],
      "properties": {
        "ontology_surface": { "type": "string" },
        "epistemics_surface": { "type": "string" },
        "deontics_surface": { "type": "string" },
        "utility_surface": { "type": "string" }
      },
      "additionalProperties": false
    },
    "authority_boundary_policy_contract": {
      "type": "object",
      "required": [
        "explicit_policy_object_required",
        "non_minting_clause_required",
        "advisory_authoritative_boundary_required"
      ],
      "properties": {
        "explicit_policy_object_required": { "const": true },
        "non_minting_clause_required": { "const": true },
        "advisory_authoritative_boundary_required": { "const": true }
      },
      "additionalProperties": false
    },
    "binding_contract": {
      "type": "object",
      "required": [
        "shared_anchor_fields_declared",
        "cross_artifact_equality_constraints_declared",
        "derivation_and_source_bindings_declared"
      ],
      "properties": {
        "shared_anchor_fields_declared": { "const": true },
        "cross_artifact_equality_constraints_declared": { "const": true },
        "derivation_and_source_bindings_declared": { "const": true }
      },
      "additionalProperties": false
    },
    "diagnostic_contract": {
      "type": "object",
      "required": [
        "diagnostics_artifact_required",
        "conformance_artifact_required",
        "aggregation_rule_explicit"
      ],
      "properties": {
        "diagnostics_artifact_required": { "const": true },
        "conformance_artifact_required": { "const": true },
        "aggregation_rule_explicit": { "const": true }
      },
      "additionalProperties": false
    },
    "deferred_seam_policy": {
      "type": "array",
      "items": {
        "enum": [
          "instantiated_here",
          "deferred_to_later_family",
          "superseded_by_alternate_surface",
          "not_selected_yet"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

## `adeu_schema_derivation_protocol@1`

```json
{
  "$id": "adeu_schema_derivation_protocol@1",
  "type": "object",
  "required": [
    "protocol_id",
    "steps",
    "forbidden_shortcuts",
    "release_gates"
  ],
  "properties": {
    "protocol_id": { "type": "string", "minLength": 1 },
    "steps": {
      "type": "array",
      "items": {
        "enum": [
          "declare_authority_layer_and_scope",
          "separate_descriptive_and_normative_claims",
          "select_primary_lineage_overlay",
          "define_family_contract",
          "define_canonical_semantic_artifact",
          "declare_odeu_realization",
          "define_cross_artifact_bindings",
          "define_project_type_contract",
          "define_diagnostics_and_conformance",
          "define_export_and_variant_contracts_if_needed",
          "declare_residuals_and_deferred_seams",
          "register_classification_evidence",
          "emit_reference_fixtures_and_validators"
        ]
      },
      "uniqueItems": true,
      "minItems": 8
    },
    "forbidden_shortcuts": {
      "type": "array",
      "items": {
        "enum": [
          "payload_before_family_contract",
          "projection_without_canonical_ir",
          "lexical_only_classification",
          "silent_authority_promotion",
          "implicit_open_residual_maps",
          "conformance_without_diagnostics_basis",
          "unbound_instance_realization"
        ]
      },
      "uniqueItems": true
    },
    "release_gates": {
      "type": "array",
      "items": {
        "enum": [
          "family_contract_complete",
          "canonical_semantic_artifact_present",
          "authority_policy_bound",
          "source_and_evidence_bindings_present",
          "diagnostics_present",
          "conformance_present",
          "reference_fixture_present",
          "registry_evidence_present"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

## `adeu_schema_alignment_report@1`

```json
{
  "$id": "adeu_schema_alignment_report@1",
  "type": "object",
  "required": [
    "subject_name",
    "assessed_against",
    "overall_status",
    "lineage_fit",
    "layer_placement",
    "aligned_elements",
    "missing_elements",
    "overconcrete_elements",
    "required_refactors"
  ],
  "properties": {
    "subject_name": { "type": "string", "minLength": 1 },
    "assessed_against": { "const": "adeu_schema_meta_grammar@1" },
    "overall_status": {
      "enum": [
        "aligned",
        "aligned_with_refactor",
        "partially_aligned",
        "mislayered",
        "not_aligned"
      ]
    },
    "lineage_fit": {
      "enum": [
        "strong_fit",
        "provisional_fit",
        "unclear_fit",
        "misfit"
      ]
    },
    "layer_placement": {
      "type": "object",
      "required": [
        "meta_level_elements",
        "family_level_elements",
        "project_type_elements",
        "instance_level_elements"
      ],
      "properties": {
        "meta_level_elements": { "type": "array", "items": { "type": "string" } },
        "family_level_elements": { "type": "array", "items": { "type": "string" } },
        "project_type_elements": { "type": "array", "items": { "type": "string" } },
        "instance_level_elements": { "type": "array", "items": { "type": "string" } }
      },
      "additionalProperties": false
    },
    "aligned_elements": {
      "type": "array",
      "items": { "type": "string" }
    },
    "missing_elements": {
      "type": "array",
      "items": {
        "enum": [
          "family_contract",
          "primary_lineage_overlay",
          "artifact_ladder",
          "authority_boundary_policy",
          "source_binding",
          "evidence_binding",
          "derivation_binding",
          "diagnostics_artifact",
          "conformance_artifact",
          "export_or_variant_artifact",
          "reference_fixture",
          "registry_evidence",
          "residual_policy"
        ]
      },
      "uniqueItems": true
    },
    "overconcrete_elements": {
      "type": "array",
      "items": { "type": "string" }
    },
    "required_refactors": {
      "type": "array",
      "items": { "type": "string" }
    },
    "risk_flags": {
      "type": "array",
      "items": {
        "enum": [
          "authority_laundering_risk",
          "evidence_underbinding_risk",
          "classification_ambiguity",
          "diagnostics_gap",
          "instance_binding_gap",
          "manual_harmonization_risk"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

## `adeu_schema_diagnostics@1`

```json
{
  "$id": "adeu_schema_diagnostics@1",
  "type": "object",
  "required": [
    "subject_name",
    "overall_severity",
    "findings"
  ],
  "properties": {
    "subject_name": { "type": "string", "minLength": 1 },
    "overall_severity": {
      "enum": ["info", "low", "medium", "high", "critical"]
    },
    "findings": {
      "type": "array",
      "items": {
        "type": "object",
        "required": [
          "finding_id",
          "severity",
          "layer",
          "finding_class",
          "message",
          "recommended_fix"
        ],
        "properties": {
          "finding_id": { "type": "string", "minLength": 1 },
          "severity": {
            "enum": ["info", "low", "medium", "high", "critical"]
          },
          "layer": {
            "enum": ["meta", "family", "project_type", "instance"]
          },
          "finding_class": {
            "enum": [
              "missing_constitutional_slot",
              "carrier_lineage_confusion",
              "authority_non_minting_gap",
              "advisory_authoritative_blur",
              "missing_family_contract",
              "missing_artifact_ladder",
              "missing_source_or_evidence_binding",
              "missing_diagnostics_or_conformance",
              "missing_instance_binding",
              "residual_escape_hatch",
              "unbounded_settlement_claim",
              "lexical_overclassification",
              "overconcrete_meta_field",
              "underconstrained_family_payload",
              "deferred_seam_not_declared"
            ]
          },
          "message": { "type": "string", "minLength": 1 },
          "recommended_fix": { "type": "string", "minLength": 1 }
        },
        "additionalProperties": false
      }
    },
    "strengths": {
      "type": "array",
      "items": { "type": "string" }
    }
  },
  "additionalProperties": false
}
```

## `adeu_schema_layer_model@1`

```json
{
  "$id": "adeu_schema_layer_model@1",
  "type": "object",
  "required": [
    "layers",
    "cross_layer_constraints"
  ],
  "properties": {
    "layers": {
      "type": "array",
      "minItems": 4,
      "maxItems": 4,
      "items": {
        "type": "object",
        "required": [
          "layer_id",
          "governs",
          "must_define",
          "must_not_define"
        ],
        "properties": {
          "layer_id": {
            "enum": [
              "L0_meta_schema",
              "L1_family_contract",
              "L2_project_type_grammar",
              "L3_instance_realization"
            ]
          },
          "governs": { "type": "string", "minLength": 1 },
          "must_define": {
            "type": "array",
            "items": { "type": "string" }
          },
          "must_not_define": {
            "type": "array",
            "items": { "type": "string" }
          }
        },
        "additionalProperties": false
      }
    },
    "cross_layer_constraints": {
      "type": "array",
      "items": {
        "enum": [
          "meta_slots_constrain_family_contracts",
          "family_contracts_constrain_project_type_grammars",
          "project_type_grammars_constrain_instance_realizations",
          "descriptive_artifacts_do_not_mint_normative_authority",
          "instance_outputs_must_bind_back_to_family_contract",
          "project_type_vocabulary_must_not_overwrite_meta_law"
        ]
      },
      "uniqueItems": true
    }
  },
  "additionalProperties": false
}
```

The practical synthesis is:

* the repo already has the pieces of a schema-authoring constitution,
* the right unit is not one mega-schema but a **family contract plus artifact ladder**,
* your prior agentic-DE framework is best treated as a **project-type semantic artifact candidate**,
* and future concrete families should be generated by filling the meta-grammar’s slot classes first, so they begin life already aligned with ADEU doctrine rather than being harmonized after the fact.
