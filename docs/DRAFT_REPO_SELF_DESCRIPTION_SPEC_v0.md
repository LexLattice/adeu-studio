# Draft Repo Self-Description Spec v0

Status: working high-level draft for a separate but connected planning direction.

Authority posture:

- this document is a support/planning-seed artifact;
- it is not a lock doc;
- it does not select the next family by itself;
- it does not authorize runtime behavior, schema release, or implementation by itself.

Related inputs:

- `REPO_ATLAS.md`
- `ADEU Recursive Self-Improvement Policy.md`
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- released `meta_*` schema/control family under `packages/adeu_core_ir/schema/`
- the currently active parallel planning branches around:
  - contest participation (`docs/DRAFT_NEXT_ARC_OPTIONS_v26.md`);
  - structural reasoning assessment (`docs/DRAFT_NEXT_ARC_OPTIONS_v27.md`)

## 1. Direct Answer

As the repo branches and its surface area increases, prose-only self-description stops
being enough.

ADEU should not only govern artifacts built by the repo.

ADEU should also emit typed, generated representations of the repo itself as an ADEU
artifact system.

That means the repo should move beyond:

- prose atlas;
- constitutional policy;
- local ad hoc inventory;
- maintainers noticing drift by continuity alone.

And toward:

- typed repo entity catalogs;
- typed schema-family registries;
- typed symbol and dependency views;
- typed test-intent mappings;
- typed optimization and drift registers.

## 2. Core Thesis

Two recursive artifacts are needed together.

First, the constitutional artifact:

- how ADEU may change itself;
- under what evidence;
- under what gates;
- under what rollback or escalation posture.

Second, the descriptive artifact:

- what the repo currently contains;
- what each surface is for;
- how surfaces relate;
- where overlap exists;
- where drift exists;
- where compression is possible.

Without the descriptive artifact, constitutional self-improvement floats too abstractly.

Without the constitutional artifact, descriptive decomposition is just inventory.

So the deeper recursive move is:

```text
repo surfaces
    -> typed ADEU-native self-description artifacts
    -> typed drift / overlap / optimization findings
    -> governed self-amendment over explicit targets
```

## 3. Repo-Grounded Basis

The repo already shows proto-self-description, but not yet full self-hosting
self-description.

Existing repo-grounded signals include:

- `REPO_ATLAS.md` as a prose navigation and subsystem-summary artifact;
- `ADEU Recursive Self-Improvement Policy.md` as a constitutional scaffold;
- `docs/DRAFT_RECURSIVE_COMPILATION_v0.md` as a higher-order note about ADEU building
  ADEU;
- released `meta_module_catalog@1`, `meta_loop_*`, `meta_control_update_candidate@1`,
  and related meta-control surfaces under `packages/adeu_core_ir/schema/`.

Those matter, but they remain uneven relative to the rest of the system.

The current repo-visible shape is already large enough that prose continuity alone is no
longer a sufficient carrier of self-understanding.

Current visible counts in this working tree are:

- `1913` repo-visible files from `rg --files`;
- `472` Python files;
- `477` Markdown files;
- `93` JSON schemas under `spec/`;
- `21` top-level package directories under `packages/`;
- `105` API test files.

Visible hotspot examples include:

- `apps/api/src/adeu_api/main.py` at `8377` lines;
- `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py` at `15622` lines.

Those counts do not prove bad design by themselves.

They do show that the repo is now large enough that:

- role classification;
- dependency visibility;
- hotspot recognition;
- and overlap/drift detection

should become typed first-class objects rather than remaining mostly tacit.

## 4. Why This Is A Separate Arc Direction

This direction is connected to recursive governance and to practical repo analysis, but
it should not be collapsed into either.

The practical repo-analysis lane asks:

- how to analyze a repo as a bounded target of observation, intent comparison, and
  alignment reporting.

The recursive-governance lane asks:

- how ADEU may amend itself without dissolving governance.

This self-description direction asks:

- how ADEU can emit an explicit typed model of its own current artifact system so later
  governance and optimization are operating over named objects rather than vague prose.

So this direction may constrain:

- future recursive amendment proposals;
- repo optimization proposals;
- hotspot and consolidation triage;
- future atlas/decomposition automation.

But it should not mint, by itself:

- recursive amendment authority;
- constitutional override rules;
- repo mutation permission;
- broad optimization doctrine beyond bounded descriptive surfacing.

## 5. The Two Planes

The self-hosting layer should be split into two planes.

### 5.1 Descriptive plane: what ADEU currently is

This plane is a generated decomposition of the repo itself.

It should answer questions such as:

- what are the authoritative entity classes of this repo?
- which files are semantic authority, implementation, evidence, fixture, or generated
  explanation surfaces?
- which modules are runtime-critical, validator-critical, schema-exporting, or helper
  surfaces?
- which tests defend which invariants?
- which schemas instantiate the same higher-order form under different names?
- where are consolidation and compression candidates visible?

### 5.2 Normative plane: how ADEU may change itself

This plane is the constitutional side.

It should build on:

- the existing recursive policy scaffold;
- the existing meta-loop and meta-control family;
- future recursive amendment lanes.

It should not operate over vague prose descriptions of the repo.

It should operate over explicit typed objects from the descriptive plane.

## 6. The Recommended First Move

The first safe move should be descriptive-plane first.

That means:

- build the self-description substrate before broad self-amendment logic;
- emit typed repo objects before proposing broad constitutional control over them;
- prefer cataloging, classification, and dependency surfacing before optimization or
  amendment automation.

The strongest immediate first-family candidates are:

- `repo_entity_catalog@1`
- `repo_schema_family_registry@1`

Those two surfaces together start turning the repo from prose-described to self-
described.

The schema corpus is likely the strongest first bounded subcorpus inside that move,
because schemas already expose:

- closed-world shape;
- anchor vocabularies;
- governance posture;
- lineage posture;
- visible recurring carrier forms.

### 6.1 Epistemic posture of descriptive outputs

The descriptive plane should not only emit typed objects.

It should also make the epistemic status of those objects explicit.

At a minimum, descriptive outputs should distinguish between:

- observed:
  directly read from filesystem, AST, import graph, test file, schema file, or other
  concrete repo surface;
- derived deterministically:
  computed from explicit deterministic rules over observed surfaces;
- inferred heuristically:
  classified from naming, location, pattern similarity, or other non-settled signals;
- adjudicated:
  reviewed or corrected by explicit human judgment;
- settled:
  accepted later through a governed release or adjudication path.

This distinction matters because a self-description artifact can look structurally clean
while still carrying uncertain internal claims.

So future descriptive artifacts should carry explicit posture for at least:

- extraction provenance;
- determinism posture;
- confidence posture;
- adjudication posture;
- snapshot scope and stale-snapshot semantics.

## 7. Repo Entity Taxonomy Axes

The repo entity model should be explicitly multi-axis.

It should not collapse carrier kind, semantic role, governance posture, derivation
posture, and mutation posture into one mixed category list.

### 7.1 Surface kind

Illustrative surface kinds include:

- doc;
- schema/spec;
- code module;
- test;
- fixture;
- generated artifact;
- app surface;
- policy surface;
- build or execution infrastructure.

### 7.2 Semantic role

Illustrative semantic roles include:

- semantic authority;
- implementation;
- evidence;
- diagnostic;
- explainer;
- planning;
- orchestration;
- validation.

### 7.3 Governance posture

Illustrative governance postures include:

- draft;
- advisory;
- released;
- locked;
- superseded;
- generated-reference-only.

### 7.4 Derivation posture

Illustrative derivation postures include:

- source;
- generated;
- compiled;
- summarized;
- extracted;
- mirrored.

### 7.5 Mutation posture

Illustrative mutation postures include:

- editable;
- generated-only;
- release-gated;
- frozen;
- fixture-stable;
- mirror-only.

### 7.6 Example applications

The important move is not only the list.

It is the typed role of each surface across axes.

Examples:

- a doc may be:
  - surface kind: `doc`;
  - semantic authority,
  - planning draft,
  - assessment,
  - generated explainer;
- a schema may be:
  - surface kind: `schema/spec`;
  - constitutive,
  - derivative,
  - export-facing,
  - internal-control,
  - meta-governance;
- a test may be:
  - surface kind: `test`;
  - invariant-guard,
  - regression,
  - parity,
  - fixture-conformance,
  - release-lint;
- a Python module may be:
  - surface kind: `code module`;
  - model-definition,
  - validation,
  - orchestration,
  - I/O glue,
  - CLI wrapper,
  - export layer,
  - consolidation-debt hotspot.

Until those roles are explicit, the repo remains understandable mainly through human
continuity.

## 8. Schema Family Registry Doctrine

Schema filenames and prefixes are not enough.

The repo should be able to ask of its schemas:

- what higher-order role-form does each schema instantiate?
- what authority layer does it occupy?
- what lineage and evidence posture does it require?
- is it source, derivative, settlement, diagnostic, manifest, request, report, trace,
  registry, contract, or something else?
- which ADEU dimensions are explicitly typed and which are left implicit?

Visible schema clusters already include:

- `adeu_arc_*`
- `adeu_architecture_*`
- `meta_*`
- `ux_*`
- `policy_*`
- `synthetic_*`

Likely higher-order recurring role-forms already visible across the repo include:

- packet;
- frame;
- manifest;
- report;
- contract;
- registry;
- trace;
- request;
- resolution;
- projection;
- delta;
- evidence.

So the deeper question is:

- did these schemas really emerge from stable meta-forms,
- or did they drift case by case while preserving naming aesthetics?

The schema registry should make that question machine-legible.

### 8.1 Schema role-form determination rules

Schema role-form classification should not remain vibe-based.

The registry should specify, in precedence order, whether role-form classification is
determined by:

1. structural signature:
   required or characteristic field patterns, object topology, reference posture, or
   other stable structural traits;
2. semantic or functional role:
   what the schema does in the artifact system when structure alone does not settle it;
3. governance role:
   whether the schema acts as source, derivative, settlement, diagnostic, request,
   report, trace, registry, contract, or similar governance object;
4. lexical naming:
   filename, schema ID, or naming family cues used only as lower-precedence support.

The registry should also make explicit:

- whether one schema may carry one primary role-form plus secondary role-form tags;
- whether the classification is mechanically derived, heuristically inferred, or
  adjudicated;
- what differentiates nearby role-forms when the boundary is not obvious.

### 8.2 Current working schema-core hypothesis

The current best branch-local hypothesis for the schema-family-registry lane is not:

- one flat universal meta-schema;
- or one fully fragmented family-per-family ontology.

The current best working hypothesis is:

```text
common core envelope
  + carrier overlays
  + lineage overlays
  + narrow named residuals
```

Under this hypothesis, the stable thing is primarily the envelope:

- discriminator posture;
- closure and local-def posture;
- anchor posture;
- governance posture;
- evidence, derivation, and lineage posture;
- settlement or boundedness posture.

Carrier variation and lineage-specific anchor vocabularies should then be modeled
explicitly rather than flattened away.

This should remain:

- a branch-local conceptual hypothesis for `V45-A`;
- not yet settled ADEU schema constitution;
- not yet sufficient for lock-level doctrine without a bounded reconstruction check.

So `V45-A` should likely require one bounded schema subset where representative schemas
are decomposed into:

- core fields;
- carrier overlay;
- lineage overlay;
- residuals;

and then explicitly reconstructed back.

## 9. Symbol, Dependency, And Test-Intent Doctrine

The same explicitness should apply to code and tests.

### 9.1 Symbol catalog

A repo-level symbol pass should make explicit:

- modules;
- classes;
- functions;
- imports and dependencies;
- linked schemas;
- linked tests;
- role classifications;
- overlap or consolidation candidates.

### 9.2 Dependency graph

The repo should surface not only import graphs, but typed dependency posture:

- runtime-critical dependency;
- validator-critical dependency;
- schema-export dependency;
- app-integration dependency;
- optional/helper dependency.

### 9.3 Test intent matrix

Tests should not be represented only as files.

They should be representable as protections over named invariants.

The repo should be able to answer:

- which invariant does each test defend?
- which schema, module, or route does it bind?
- is it guarding ontology, epistemics, deontics, utility, or a mix?
- is it release-gating or advisory?
- what drift becomes possible if it is removed?

The matrix should also preserve the distinction between:

- claimed invariant binding:
  what the test is intended to defend;
- observed assertion surface:
  what the test actually checks in code;
- confidence posture:
  how strongly the observed assertions justify the claimed invariant link.

## 10. Optimization Register Doctrine

Optimization should not begin as "make the code smaller."

It should begin as:

- improve the ratio between semantic explicitness and maintenance burden without losing
  governance.

The optimization register should separate at least:

- structural compression:
  fewer duplicated abstractions;
- semantic compression:
  fewer distinct patterns expressing the same law;
- governance compression:
  fewer places where the same invariant is restated inconsistently;
- surface compression:
  fewer hotspots whose behavior must be reconstructed from long files manually.

It should also allow typed posture such as:

- hotspot;
- consolidation candidate;
- justified monolith;
- temporary concentration;
- forbidden drift zone.

### 10.1 Diagnostic-to-amendment boundary

Optimization findings are diagnostic objects, not mutation entitlements.

So the family should make explicit that:

- optimization findings do not imply mutation permission;
- hotspot status does not imply split entitlement;
- duplication signals do not imply abstraction entitlement;
- surfaced consolidation candidates do not imply merge entitlement;
- only separately governed amendment artifacts may convert diagnosis into mutation.

## 11. Candidate Artifact Family

The first family should likely emit a bounded, descriptive artifact set.

Illustrative candidate artifacts are:

- `repo_entity_catalog@1`
- `repo_schema_family_registry@1`
- `repo_symbol_catalog@1`
- `repo_test_intent_matrix@1`
- `repo_dependency_graph@1`
- `repo_optimization_register@1`

These names are planning-level candidate names, not frozen lock-level schema IDs.

### 11.1 Candidate artifact roles

`repo_entity_catalog@1`:

- catalogs repo surfaces and assigns typed entity classes and role posture.

`repo_schema_family_registry@1`:

- classifies schemas by family, role-form, authority layer, lineage posture, and
  evidence posture.

`repo_symbol_catalog@1`:

- catalogs code symbols, imports, linked schemas/tests, and overlap signals.

`repo_test_intent_matrix@1`:

- maps tests to invariants, guarded surfaces, and gating posture.

`repo_dependency_graph@1`:

- captures typed inter-surface dependency structure rather than only raw imports.

`repo_optimization_register@1`:

- records surfaced hotspots, consolidation candidates, compression opportunities, and
  drift-sensitive maintenance burdens without, by itself, authorizing mutation.

## 12. Relationship To Existing Meta-Control Surfaces

The repo already has released meta-control and meta-loop surfaces.

That family should be read as:

- early constitutional and loop-governance scaffolding;
- not yet a whole-repo self-description substrate.

So this new descriptive family should not reopen those released meta artifacts.

Instead it should provide better explicit objects for future recursive-governance lanes
to reference.

Short form:

- descriptive plane first;
- normative plane later binds to descriptive plane outputs.

## 13. First Safe Family Shape

The first bounded family should stop at descriptive extraction and classification.

The safe first move is likely:

- define repo entity catalog surfaces;
- define schema family registry surfaces;
- define deterministic extraction and fixture posture;
- define extraction provenance and confidence posture;
- define human-adjudication posture for non-mechanical classifications;
- define stale-snapshot semantics over moving repo state;
- stop before broad symbol-level optimization, recursive amendment, or mutation
  authority.

In short:

```text
first make the repo explicitly self-described, then let recursive governance operate on
that description
```

## 14. Non-Goals

This direction should not initially aim to:

1. authorize automated repo self-modification;
2. collapse descriptive decomposition and constitutional governance into one artifact;
3. infer broad optimization prescriptions from hotspot signals alone;
4. replace human judgment with a raw repo-inventory dump;
5. claim that every repeated helper or large file must be merged or split immediately.

## 15. Planning-Seed Acceptance Criteria

This high-level seed is mature enough to feed next-arc planning only if it can support:

1. a clear split between descriptive self-model and normative recursive governance;
2. a repo-grounded claim that prose-only atlas/policy surfaces are no longer enough;
3. explicit epistemic posture doctrine for descriptive outputs:
   observed, derived, inferred, adjudicated, and settled;
4. explicit multi-axis entity taxonomy rather than mixed category lists;
5. explicit schema-family role-form classification rather than filename clustering only;
6. explicit schema role-form determination rules with precedence across structural,
   semantic, governance, and lexical cues;
7. explicit test-intent and dependency visibility as first-class descriptive objects;
8. explicit distinction between claimed invariant binding and observed assertion surface
   in the test-intent matrix;
9. explicit optimization-register doctrine richer than generic refactoring talk;
10. an explicit diagnostic-to-amendment boundary so descriptive findings do not self-
    authorize mutation;
11. a bounded descriptive-first family shape before constitutional amendment widening;
12. candidate artifact outputs for entity catalog, schema registry, symbol catalog, test
    intent matrix, dependency graph, and optimization register.

## 16. Suggested Follow-On Docs

If this direction is selected for next-arc planning, the next bundle should probably be:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`
- `docs/DRAFT_REPO_ENTITY_ROLE_TAXONOMY_v0.md`
- `docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md`
- one architecture/decomposition draft if a concrete family label is selected
- only later a recursive-governance binding draft over the emitted descriptive surfaces

No concrete family/path label is selected by this document.

## 17. Machine-Checkable Seed Summary

```json
{
  "schema": "repo_self_description_seed@1",
  "artifact": "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support_planning_seed",
  "selects_next_family": false,
  "authorizes_runtime_or_schema_release": false,
  "general_module_theme": "repo_self_description_before_recursive_amendment_widening",
  "descriptive_plane_and_normative_plane_non_equivalent_required": true,
  "descriptive_plane_first_required": true,
  "repo_grounded_scale_claim_required": true,
  "descriptive_output_epistemic_postures": [
    "observed",
    "derived_deterministically",
    "inferred_heuristically",
    "adjudicated",
    "settled"
  ],
  "extraction_provenance_required": true,
  "determinism_posture_required": true,
  "confidence_posture_required": true,
  "human_adjudication_posture_required": true,
  "stale_snapshot_semantics_required": true,
  "entity_role_typing_required": true,
  "entity_taxonomy_axes_required": [
    "surface_kind",
    "semantic_role",
    "governance_posture",
    "derivation_posture",
    "mutation_posture"
  ],
  "schema_role_form_registry_required": true,
  "schema_role_form_precedence_required": [
    "structural_signature",
    "semantic_function",
    "governance_role",
    "lexical_naming"
  ],
  "symbol_catalog_planned": true,
  "test_intent_matrix_planned": true,
  "test_intent_claimed_vs_observed_assertion_distinction_required": true,
  "dependency_graph_planned": true,
  "optimization_register_planned": true,
  "diagnostic_findings_non_promotional_required": true,
  "first_safe_family_outputs": [
    "repo_entity_catalog@1",
    "repo_schema_family_registry@1"
  ],
  "candidate_artifacts": [
    "repo_entity_catalog@1",
    "repo_schema_family_registry@1",
    "repo_symbol_catalog@1",
    "repo_test_intent_matrix@1",
    "repo_dependency_graph@1",
    "repo_optimization_register@1"
  ],
  "automatic_repo_mutation_initially_deferred": true,
  "recursive_amendment_binding_initially_deferred": true,
  "source_docs": [
    "REPO_ATLAS.md",
    "ADEU Recursive Self-Improvement Policy.md",
    "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
    "docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md"
  ]
}
```

## 18. Compressed Theorem

ADEU should not only govern artifacts built by the repo.

ADEU should govern the explicit representation, diagnosis, and later amendment of the
repo as an ADEU artifact system.

The first safe move is therefore not broad self-modification.

It is a typed, generated, descriptive self-model of the repo itself.
