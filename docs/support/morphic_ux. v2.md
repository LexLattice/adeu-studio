Used the uploaded baseline as the retained source for this hardening pass. 

## 1. Hardened complete `MORPHIC_UX_V0_ARCHITECTURE_NOTE.md`

````markdown
# MORPHIC_UX_V0_ARCHITECTURE_NOTE.md

## 1. Status / Scope

**Status:** v0 architecture note.

**Scope:** This note formalizes **Morphic_ux** as a repo-grounded doctrine for UI/UX projection in ADEU Studio. It is not an implementation pass, not a redesign of all existing UX schemas, and not a claim that the current runtime already implements the full architecture. It consolidates the existing UX governance substrate into a clearer typed projection architecture and adds a compact normative core around layers, invariants, projection lifecycle, validation surfaces, and geometry/style separation.

**Source posture:** The current repo remains authoritative. Existing schemas, fixtures, tests, frontend skill documents, and app surfaces are treated as the grounded substrate. The visual schema concepts supplied for this task clarify a doctrine over that substrate; they do not override schema contents, fixture truth, tests, or source-grounding policy.

**Body / appendix posture:** Sections 1-17 are doctrine and compile guidance. Appendix A is the repo-grounding substrate ledger. The appendix preserves path anchors and current gaps, but appendix rows do not by themselves authorize new schemas, runtime rewrites, or broad implementation work.

| Category | Meaning in this note |
|---|---|
| Already exists in the repo | UX governance schemas, v61-v65 fixture family, conformance/diagnostics, ergonomics schemas, frontend skill doctrine, artifact-inspector reference surface, prototype and Codex composer surfaces. |
| Newly clarified by the visual schema | The five-layer Morphic_ux split, explicit invariant vocabulary, separate validation surfaces, and the Codex composer bottom-band example as geometry law rather than “make it look right.” |
| Added as v0 architecture doctrine | “Do not patch surfaces”; model visible UI as one instantiated typed projection; separate semantic supply, entity grammar, interaction behavior, geometry physics, and style variables; treat screenshots/images as evidence witnesses, not authority. |
| Future work | Small fixtures/schema extensions only where existing UX governance and ergonomics artifacts cannot express the needed composer geometry, semantic supply map, or validation-surface decomposition. |

## 2. Thesis

**Morphic_ux is governed surface morphism over typed semantic structure.** A UI surface is not a bundle of patched pixels; it is an instantiated projection from deeper semantic supply, UI entity grammar, interaction transformations, spatial/geometric physics, and downstream aesthetic variables. The visible UI at moment `x` is only one lawful projection of those layers. Style is downstream of invariants. Geometry must be tested separately from style. Backend semantic transformations must be tested separately from UI behavior and layout. Images and screenshots may witness what happened, but they do not become authority by themselves.

## 3. Morphic_ux v0 laws

These laws are the compact normative core. A Codex/GPT worker should apply them before proposing fixture, schema, CSS, or runtime changes.

1. **Semantic supply before surface exposure.** A surface may expose only data/actions whose source, wiring, authority, mutability, and derivation posture are known.
2. **Entity type before visual widget.** A widget label, DOM element, CSS class, or screenshot appearance does not replace typed entity class and authority posture.
3. **Interaction contract before event patch.** Click, select, close, focus, hover, resize, submit, rollback, and failure behavior must be governed by declared preconditions and visible consequences.
4. **Geometry law before responsive CSS tweak.** Responsive layout changes must preserve named region relations, containment, docking, non-overlap, reachability, and targetability before visual tuning.
5. **Style variable after invariant preservation.** Color, typography, spacing, icon treatment, border, motion, and emphasis are free only after constitutional and instantiated invariants are preserved.
6. **Screenshot/image as witness, never authority.** Screenshots and images live under E as evidence witnesses; they cannot create D authority or override fixtures, schemas, tests, or source-grounding.
7. **Validation surfaces must be separated.** Semantic, entity, interaction, geometry, style/readability, and conformance failures must not be collapsed into one generic “UX” result.
8. **Aesthetic variables become D-binding only by explicit authority elevation.** A style variable becomes mandatory only when an authority layer, invariant, ergonomic floor, accessibility floor, or state contract elevates it.
9. **U may optimize only inside D-preserved invariants.** Visual salience, density, efficiency, and operator speed are utility optimizations, not licenses to weaken authority, evidence, state truth, or geometry law.
10. **No new schema unless fixture-level expression fails without ambiguity.** Prefer existing schemas and fixtures first. Promote a new schema only after repeated cross-surface need or after existing schemas cannot express the requirement without ambiguity.

## 4. Projection lifecycle

Morphic_ux work should compile from upstream semantics to validated surface in this order:

```text
semantic supply
  → entity grammar
  → interaction transformation contract
  → geometry physics profile
  → aesthetic variable set
  → validation surface report
  → conformance/admission
```

| Step | Product | Must not be skipped |
|---|---|---|
| `semantic supply` | A map of available data/actions, wiring, authority, mutability, derivation, provenance, and missing capability boundaries. | Do not expose a control, datum, status, or claim before its upstream supply posture is known. |
| `entity grammar` | Typed UI objects: inputs, read-only displays, buttons, menus, panels, regions, lanes, evidence surfaces, gates, status surfaces, composer subregions. | Do not substitute visual widgets for semantic entity classes. |
| `interaction transformation contract` | Declared event/state transformations, preconditions, visible consequences, gate behavior, rollback/failure posture, and user/system transition distinctions. | Do not patch events directly in runtime code before the lawful transformation is named. |
| `geometry physics profile` | Region relations, containment, docking, overlay, adjacency, non-overlap, viewport morphs, same-context reachability, targetability, and measurement obligations. | Do not treat responsive CSS as the source of geometry authority. |
| `aesthetic variable set` | Downstream style variables and any explicit authority elevations that make style D-binding. | Do not use color, spacing, motion, or emphasis to launder an invariant. |
| `validation surface report` | Separate findings for semantic supply, entity behavior, interaction, geometry, style/readability, and conformance/reporting. | Do not accept a single screenshot, broad UI test, or generic diagnostic as sufficient. |
| `conformance/admission` | A fail-closed admission decision grounded in source refs, fixtures, tests, and diagnostics. | Do not admit a projection because it looks plausible or because a concept is interesting. |

## 5. Non-goals

Morphic_ux v0 is not:

- a design system;
- a renderer rewrite;
- a screenshot-based authority system;
- a replacement for existing UX governance schemas;
- a full ergonomic adjudicator;
- a mandate to create a monolithic schema universe;
- a claim that all current app surfaces already comply;
- a license to generalize from prototypes without source-grounded fixtures;
- a reason to promote every useful concept into schema immediately.

The v0 posture is conservative: clarify doctrine, preserve repo grounding, prefer fixtures, and add only the smallest typed substrate that repeated evidence demands.

## 6. Core doctrine vs substrate ledger

The main body of this note is the doctrine workers should apply. Appendix A is the substrate ledger workers should consult for repo grounding.

| Main-body concern | Doctrine role | Appendix role |
|---|---|---|
| Laws and lifecycle | Define compile order and fail-closed rules. | Shows existing anchors that partially support the laws. |
| Layer model | Defines the five Morphic_ux layers. | Maps current schemas, fixtures, tests, skills, and app surfaces to those layers. |
| Invariant model | Defines constitutional invariant, instantiated invariant, aesthetic variable, illegal laundering, and authority elevation. | Identifies repo artifacts that already carry invariants, authority posture, evidence, or ergonomic floors. |
| Validation surfaces | Requires semantic/entity/interaction/geometry/style/conformance separation. | Identifies current diagnostics, conformance, ergonomics, and governance evidence substrates. |
| Schema admission | Blocks schema sprawl and requires fixture-first expression. | Records gaps that may motivate future small fixtures or schema extensions but do not authorize them alone. |

A worker should read the body as doctrine and the appendix as grounding evidence. The appendix is intentionally long so that the doctrine stays short without losing repo specificity.

## 7. ODEU interpretation

Morphic_ux should be read in ODEU terms, not as a conventional design-system layer cake.

| ODEU axis | Morphic_ux meaning | Examples in current repo |
|---|---|---|
| **O — Ontology** | The objects being projected: UI objects, entity classes, layout regions, lanes, action clusters, state surfaces, surface identities, composer regions, menus, input fields, evidence lanes, commit gates. | `ux_morph_ir.v1.json` ontology; `ux_surface_projection.v1.json` regions/lanes/action clusters/state surfaces; artifact-inspector reference surface; Codex composer surfaces. |
| **E — Epistemics** | Evidence about what exists and what happened: measurements, screenshots, traces, source-grounded refs, binding/provenance hooks, runtime measurement evidence, tests. | v63 rendered surface contract; governance evidence tests; ergonomic runtime measurement evidence and bridge report; app source code. |
| **D — Deontics** | What must or must not be true: invariants, authority constraints, interaction obligations, evidence-before-commit, visibility constraints, accessibility/ergonomic floors, no visual authority inflation. | `ux_morph_ir.v1.json` deontics/invariants; source-grounding authority policy; ergonomics rule authority stack; governance fail-closed tests. |
| **U — Utility** | Why the projection is valuable for the user: task fit, trust calibration, error prevention, visual salience, operator speed, cognitive load, density tradeoffs. | `ux_domain_packet.v1.json` utility ranking; approved profile table; morph axes; ergonomic candidate profiles. |

Screenshots and images live under **E** as witnesses. They may show that a projection instance looked or behaved a certain way. They do not by themselves become **D** authority and cannot override typed invariants, source-grounding rules, schema fixtures, or tests.

## 8. Layer model

### 8.1 Upstream Capability / Data

| Field | Definition |
|---|---|
| Purpose | Define the semantic supply of the UX: available data, available actions, actual wiring, authoritative vs mutable vs derived material, and whether a user-facing control is backed by real capability. |
| Primitive objects | Data source, semantic packet, action capability, mutation boundary, derivation, authority source, provenance ref, backend transformation, API route, fixture ref. |
| Inputs | Domain packet, backend/API contracts, fixtures, source-grounding docs, app source, agentic surface authority descriptors where write/execute surfaces are exposed. |
| Outputs | A semantic supply map for the projection: what the UI may display, what it may request, what it may mutate, what it must mark as derived or advisory, and what is not actually wired. |
| Invariants | UI must not mint authority; UI must not expose an action as live if it is not wired; authoritative/mutable/derived/advisory material must not collapse visually or semantically; conceptually possible data is not the same as actually wired data. |
| Validation surface | Backend semantic transformation tests, fixture validation, API/action contract tests, provenance checks, missing-data and missing-action failure cases. |
| Existing repo anchors | `ux_domain_packet.v1.json`; v61 domain fixture; source-grounding authority policy; `ux_governance.py`; governance evidence tests; agentic surface authority schemas for adjacent write surfaces; Codex workbench send/action source where relevant. |
| Open gaps | No first-class `UxSemanticSupplyMap` currently enumerates available data/actions with `wired`, `authoritative`, `mutable`, and `derived` status for arbitrary UX surfaces. |

### 8.2 UI Entity Grammar

| Field | Definition |
|---|---|
| Purpose | Define the typed UI ontology that can be projected: input fields, read-only displays, buttons, menus, pop-ups, panels, tabs, badges, regions, lanes, state surfaces, commit gates, evidence surfaces, and composer subregions. |
| Primitive objects | Entity class, widget role, semantic kind, lane, region, action cluster, state surface, evidence surface, component ergonomic class, visibility contract, stable binding. |
| Inputs | Morph IR ontology, surface projection, domain task posture, visibility contract, ergonomic registry, semantic supply map. |
| Outputs | Entity grammar registry for a surface family, including which objects exist, what semantic class they carry, what authority posture they express, and where they may appear. |
| Invariants | Advisory, authoritative, diagnostic, provisional, warning, and commit objects must remain distinct; a widget term must not replace semantic typing; an input field is not merely a styled textarea if it carries prompt/command semantics; a button is not merely decoration if it triggers capability. |
| Validation surface | Entity behavior tests, binding/provenance coverage, visibility-contract tests, semantic-kind matching, component class checks. |
| Existing repo anchors | `ux_morph_ir.v1.json`; `ux_surface_projection.v1.json`; `ux_component_visibility_contract.v1.json`; `ux_component_ergonomic_registry.v1.json`; artifact-inspector page/reference surface; Codex composer surfaces. |
| Open gaps | Current UX governance vocabulary is strong for the artifact-inspector family but does not yet provide a reusable grammar for dropdowns, popups, menu checkmarks, composer input/bottom/send regions, panels, tabs, and badges as first-class Morphic_ux objects. |

### 8.3 Interaction / Transformations

| Field | Definition |
|---|---|
| Purpose | Define behavioral algebra: click, select, close, focus, hover, resize, state propagation, user-driven changes, system-driven changes, runtime requests, visible consequences, rollback, and failure surfaces. |
| Primitive objects | Surface event, transition, precondition, visible consequence, runtime effect request, truth posture, reversible flag, gate source, rollback path, failure surface, success surface, outside-click close law, selection propagation law. |
| Inputs | Entity grammar registry, semantic supply map, interaction contract, current state, runtime capability response. |
| Outputs | Interaction transformation contract describing how user/system events lawfully change state and what the user must see as a result. |
| Invariants | State transitions must be observable; selected items must update immediately unless explicitly modeled otherwise; menus/popups must close according to contract; disabled/gated actions must expose why they are unavailable; user-driven and system-driven changes must not be conflated. |
| Validation surface | Interaction tests, state propagation tests, event contract tests, rollback/failure tests, same-context tests. |
| Existing repo anchors | `ux_interaction_contract.v1.json`; v62 interaction fixture; governance v36b/evidence tests; Codex composer send/toggle behavior sources. |
| Open gaps | Existing interaction contract does not yet enumerate generic `select`, `close_on_outside_click`, `hover`, `resize`, dropdown checkmark updates, or overlay dismissal as reusable Morphic_ux transformation primitives. |

### 8.4 Spatial / Geometric Physics

| Field | Definition |
|---|---|
| Purpose | Define lawful spatial relationships independent of style: layout regions, containment, docking, overlay, non-overlap, adjacency, resizing, reflow, viewport mode, fullscreen/windowed/narrow invariants, and measurable geometry floors. |
| Primitive objects | Region, lane, container, overlay, dock edge, adjacency relation, containment relation, z-order constraint, min/max rect, reflow rule, viewport state, measured bounding box, targetability floor. |
| Inputs | Surface projection, entity grammar, ergonomic case envelope, component visibility contract, candidate projection profile, runtime measurement evidence. |
| Outputs | Geometry physics profile for a projection instance or family, plus runtime geometry evidence and drift reports. |
| Invariants | Required evidence/status/trust surfaces remain same-context reachable; required components remain targetable/readable; bottom bands do not overlay input regions unless explicitly lawful; send/submit regions do not drift into unrelated regions; fullscreen/windowed/narrow morphs preserve declared relations. |
| Validation surface | Geometry/physics tests using measured rectangles, resize traces, component visibility, runtime bridge reports, non-overlap/containment assertions, targetability/readability floors. |
| Existing repo anchors | `ux_surface_projection.v1.json` responsive behaviors; ergonomic case/rule/candidate/runtime schemas; artifact-oriented design support artifacts; artifact-inspector CSS grid; Codex composer CSS/source surfaces. |
| Open gaps | No minimal `UxGeometryPhysicsProfile` currently expresses general geometry laws such as composer `input_region` containing prompt entry, `bottom_band_region` docked below input, `send_submit_region` anchored inside the bottom band, and preserved relations across fullscreen/windowed/narrow states. |

### 8.5 Surface Style / Aesthetic Variables

| Field | Definition |
|---|---|
| Purpose | Define downstream presentation variables that may change without violating semantic, entity, interaction, or geometry invariants. |
| Primitive objects | Color token, typography token, spacing token, icon treatment, border/radius, motion feel, emphasis level, CSS token map, readability floor, aesthetic variable declaration. |
| Inputs | Invariant ledger, entity grammar, geometry profile, ergonomic floors, compiler export, style tokens. |
| Outputs | Aesthetic variable set and style/readability evidence. |
| Invariants | Style cannot obscure authority, state truth, evidence, gate posture, targetability, readability, or geometry relations. Aesthetic changes cannot convert provisional material into authoritative-looking material or hide required evidence. |
| Validation surface | Style/readability tests, accessibility checks, contrast/acuity floors, visual-state distinction checks, ergonomic runtime measurement where applicable. |
| Existing repo anchors | `ux_surface_compiler_export.v1.json` CSS token map payloads; `ux_ergonomic_candidate_projection_profile_table.v1.json` free aesthetic variable declaration; CSS modules; diagnostics seeded violations around visual authority inflation and provisional authoritative styling. |
| Open gaps | No standalone `UxAestheticVariableSet` or invariant-to-token ledger currently distinguishes free variables from D-binding style obligations across all surfaces. |

## 9. Invariant model

### 9.1 Constitutional invariant

A **constitutional invariant** says what the object is. It binds the object’s identity, authority posture, semantic class, or required role before a particular rendered instance is considered.

Examples:

- A commit gate is a commit/approval gate, not a merely prominent button.
- An evidence lane required before commit is an evidence lane, not optional decorative content.
- A provisional state surface is provisional, not authoritative.
- A composer declared as a prompt-entry composer has at least an input region and a submit/action region.
- A trust boundary marker is a trust boundary marker, not an aesthetic divider.

Current repo anchors include `ux_morph_ir.v1.json` invariants/deontics, `ux_surface_projection.v1.json` state surfaces and action clusters, source-grounding frozen invariants, and governance tests that reject authority-policy drift.

### 9.2 Instantiated invariant

An **instantiated invariant** says how the object must behave in a specific projection instance or mode. It applies to the concrete surface at runtime: desktop, narrow viewport, fullscreen, windowed, expanded, collapsed, active, disabled, loading, or ambiguous.

Examples:

- A selected dropdown item must update its checkmark immediately after selection.
- A menu that opens as an overlay must close on outside click if that is the declared close law.
- A disabled send button must remain visibly disabled and explain its gate source when the contract requires that posture.
- A composer bottom band must remain below or lawfully docked to the input region in fullscreen, windowed, and narrow modes.
- A responsive projection may reflow lanes, but it may not insert a route transition where same-context reachability is required.

### 9.3 Aesthetic variable

An **aesthetic variable** is allowed to morph after constitutional and instantiated invariants are preserved. Examples include color, type scale, spacing, icon treatment, border radius, and motion feel.

Aesthetic variables are not meaningless. They remain downstream variables unless elevated by an authority layer. A color token may be free in one context and D-binding in another if it carries truth-state contrast, ergonomic readability, or authority posture.

### 9.4 Illegal invariant laundering

**Illegal invariant laundering** occurs when a required invariant is disguised as style, preference, visual cleanup, or screenshot plausibility to avoid deontic force.

Examples:

- Hiding required evidence because the layout looks cleaner.
- Moving a send button into the wrong region because it balances the visual composition.
- Styling provisional material as authoritative because the color palette is simpler.
- Treating a screenshot that “looks correct” as proof that source-grounded authority, data wiring, or geometry law is satisfied.
- Collapsing advisory and commit actions into one visual cluster without typed authority separation.
- Reclassifying a geometry relation as a responsive preference to avoid a containment/non-overlap assertion.

### 9.5 Elevating an aesthetic variable into D-binding force

An aesthetic variable becomes D-binding only when an authority layer elevates it. That elevation must be explicit and source-grounded.

Examples:

- An ergonomic rule authority stack may elevate minimum target size, text readability, contrast, or component visibility into a hard floor.
- A repo-local policy may require advisory and authoritative controls to remain visually distinguishable.
- A state-surface contract may require warning, provisional, authoritative, and diagnostic states to remain materially distinguishable.
- An accessibility or platform floor may make typography, spacing, or contrast non-optional.

The useful rule is simple: **free style can morph; D-binding style must be validated.**

## 10. Validation surfaces

Morphic_ux validation should be decomposed. A single screenshot diff or broad “UX test” is not enough.

| Validation surface | What it tests | Example failure |
|---|---|---|
| Backend / semantic transformations | Whether data/actions exist, are wired, carry correct authority/mutability/derivation, and transform correctly before UI projection. | Backend data missing; action advertised but not wired; derived value shown as authoritative source data. |
| Entity behavior | Whether typed UI objects exist, have correct semantic class, preserve authority posture, expose required state, and use lawful bindings. | Dropdown exists as styled DOM but lacks semantic selection state; read-only display behaves like editable input; commit button is visually collapsed with advisory action. |
| Interaction / transformations | Whether events produce immediate, visible, reversible or irreversible state changes according to contract. | Dropdown checkmark updates only after menu reopen; menu does not close on outside click; disabled send button appears active; rollback path invisible. |
| Geometry / physics | Whether regions maintain containment, adjacency, docking, non-overlap, same-context reachability, targetability, and resize/reflow invariants. | Bottom band overlays composer input in windowed mode; send button moves to the wrong region; evidence/status lane disappears across viewport modes. |
| Surface style / readability | Whether style variables preserve authority distinctions, visual salience, readability, acuity, and contrast without laundering invariants. | Color/style changes obscure warning vs authoritative states; type scale drops below readable floor; motion implies success before runtime confirmation. |
| Conformance / reporting | Whether diagnostics, report aggregation, source refs, provenance pointers, schema mirrors, and compiler exports remain deterministic and source-grounded. | Conformance report uses route-local heuristics; rendered contract claims authority without accepted source refs; compiler export accepts non-pass conformance gate. |

Validation examples from the visual schema should be classified this way:

- **Backend data missing** is an upstream semantic supply failure, not a CSS failure.
- **Dropdown state updates only after reopen** is an interaction/state propagation failure, not a style failure.
- **Menu not closing on outside click** is an interaction transformation failure and possibly an overlay contract failure.
- **Bottom band overlays input in windowed mode** is a geometry/physics failure.
- **Send button moves to wrong region** is a geometry/entity placement failure.
- **Color/style changes obscure invariants** is a style/readability failure and may become a deontic failure if authority or state distinctions are obscured.

Images and screenshots can help document these failures, but they are evidence inputs. They do not replace the typed validation surface.

## 11. Running example: Codex composer bottom band

The repo already contains multiple Codex-style composer surfaces, including:

- `apps/gptpro-codex-workbench/src/app/codex-workbench/codex-workbench-client.tsx`
- `apps/gptpro-codex-workbench/src/app/codex-workbench/page.module.css`
- `apps/codex-review-shell/src/renderer/codex-surface.html`
- `apps/codex-review-shell/src/renderer/codex-surface.css`
- `apps/codex-review-shell/src/renderer/codex-surface.js`
- `apps/opus-codex-workbench/src/components/conversation.js`
- `apps/opus-codex-workbench/src/styles/conversation.css`
- `apps/gpt54-codex-workbench/src/renderer/app.ts`
- `apps/gpt54-codex-workbench/src/renderer/styles.css`

These surfaces show real composer anatomy: prompt textarea/input, context buttons, metadata/hints, toolbar/footer rows, and send/submit controls. They are useful repo witnesses. They do not yet constitute a first-class Morphic_ux composer geometry fixture.

### 11.1 Architecture-level object model

A Codex composer should be modeled as explicit regions, not as a patch to a bottom strip of pixels:

| Composer object | Layer | Role |
|---|---|---|
| `composer_root` | Entity + geometry | Bounded composer surface containing input, band, submit, context/status subregions. |
| `input_region` | Entity + geometry | Prompt entry area; must remain editable, legible, and not occluded by the bottom band. |
| `bottom_band_region` | Geometry | Docked/footer region carrying context controls, metadata, secondary actions, or hints. |
| `send_submit_region` | Entity + interaction + geometry | Submit action; must remain targetable, correctly gated, and in the declared composer/action region. |
| `context_action_region` | Entity + interaction | Optional context buttons/tabs such as files, diff, terminal, workflow, or review. |
| `option_menu_region` | Entity + interaction + overlay geometry | Dropdown/menu surface; selection state and close law must be explicit. |
| `status_metadata_region` | Entity + style/readability | Runtime or session status; may be compact, but cannot obscure gating or authority truth. |

### 11.2 Required invariants

At v0 doctrine level, the composer example introduces these typed invariants:

- The input region and bottom band are distinct regions.
- The bottom band may dock to the input region, but it must not unlawfully overlay the input region.
- The send/submit region belongs to the composer action/bottom band relation and must not drift to an unrelated surface region.
- Disabled or unavailable submit state must remain observable where the interaction contract requires it.
- Dropdown menus must close on outside click when that is the declared close law.
- Dropdown checkmarks or selected state indicators must update immediately after selection unless a contract explicitly models deferred state.
- Fullscreen, windowed, and narrow modes must preserve the same lawful geometric relations: containment, adjacency, non-overlap, targetability, and reachability.
- Style may change the feel of the composer, but style may not hide the composer’s semantic input/action/status geometry.

The correct abstraction is therefore not **“make it look right in fullscreen.”** The correct abstraction is:

> Define composer geometry so input, bottom band, and send/submit regions maintain lawful relations across viewport states.

This is architecture-level doctrine. It does not require a broad runtime rewrite. The next useful repo artifact would be a small fixture demonstrating this composer-region law.

### 11.3 Minimal composer geometry fixture skeleton

This skeleton is a fixture candidate, not a schema mandate. It should be attempted as fixture-level expression before any new `UxGeometryPhysicsProfile` schema is proposed.

```text
composer_geometry_fixture@v0
  viewports:
    - fullscreen
    - windowed_medium
    - windowed_narrow

  regions:
    - composer_root
    - input_region
    - bottom_band_region
    - send_submit_region
    - option_menu_region
    - status_metadata_region

  assertions:
    - input_region is not occluded by bottom_band_region
    - bottom_band_region remains docked/contained relative to composer_root
    - send_submit_region remains targetable and in the declared action region
    - option_menu_region closes on outside click when close law requires it
    - selected menu option updates visible state immediately after selection
    - fullscreen/windowed/narrow modes preserve declared region relations
```

The fixture should remain conceptual until a next slice chooses the exact existing schema/fixture home. It should not introduce a monolithic composer runtime, and it should not require a renderer rewrite.

## 12. Proposed v0 object family and schema admission rule

This object family is conceptual for the architecture note. It should be mapped to existing schemas first and materialized as new schema only where the gap is real.

**Schema admission rule:** Prefer fixture-level expression first. Promote to a new schema only after repeated cross-surface need or after an existing schema cannot express the requirement without ambiguity.

Corollaries:

- No new Morphic_ux schema just because the concept is interesting.
- No monolithic `MorphicUxEverythingProfile`.
- Prefer small, typed additions over broad profile universes.
- Every new schema eventually needs acceptance fixtures and rejection fixtures / negative cases.
- Schema promotion should fail closed when the need can be represented by existing fixtures, existing schemas, or documentation-only doctrine.

| Proposed object | Purpose | Existing mapping | v0 status |
|---|---|---|---|
| `MorphicUxProjectionProfile` | Names an approved projection posture across domain, morph axes, topology, profile variants, and conformance gate. | Partly maps to v61 approved profile table, `ux_morph_ir.v1.json` morph axes, `ux_surface_compiler_variant_manifest.v1.json`, and v65 compiler exports. | Conceptual consolidation. No immediate new schema required. Do not create a monolithic profile. |
| `UxSemanticSupplyMap` | Enumerates available data/actions, actual wiring, authority, mutability, derivation, and provenance. | Partly maps to `ux_domain_packet.v1.json`, source-grounding authority policy, backend/app source, and agentic surface descriptors where relevant. | Useful only if fixtures cannot distinguish possible data from wired data without ambiguity or if repeated surfaces need the distinction. |
| `UxEntityGrammarRegistry` | Defines reusable UI entity classes: input fields, read-only displays, buttons, menus, pop-ups, panels, tabs, badges, regions, lanes, state surfaces. | Partly maps to `ux_morph_ir.v1.json`, `ux_surface_projection.v1.json`, `ux_component_visibility_contract.v1.json`, and `ux_component_ergonomic_registry.v1.json`. | Possible small extension or fixture vocabulary, not a design-system schema and not a widget taxonomy universe. |
| `UxInteractionTransformationContract` | Extends interaction contract vocabulary to include click/select/close/focus/hover/resize, outside-click closure, immediate selection propagation, and user/system-driven transitions. | Maps directly to `ux_interaction_contract.v1.json`. | Existing schema covers the family pattern; extension is conditional on fixture expression failing without ambiguity. |
| `UxGeometryPhysicsProfile` | Defines containment, docking, overlay, adjacency, non-overlap, reflow, fullscreen/windowed/narrow invariants, and measured geometry obligations. | Partly maps to `ux_surface_projection.v1.json`, ergonomic case/rule/candidate/runtime schemas, and artifact-oriented support artifact doctrine. | Most likely useful only if composer geometry cannot be expressed through current surface projection + ergonomics fixtures. Conditional, not automatic. |
| `UxInvariantLedger` | Consolidates constitutional invariants, instantiated invariants, aesthetic variables, elevation authority, and illegal laundering checks. | Partly maps to `ux_morph_ir.v1.json` invariants/deontics/epistemics, source-grounding invariants, ergonomics rule authority stack, and conformance diagnostics. | Conceptual v0 doctrine. Keep as note unless repeated fixtures need a ledger object. |
| `UxAestheticVariableSet` | Declares downstream style variables and identifies which variables are free vs D-binding. | Partly maps to `ux_surface_compiler_export.v1.json` CSS token maps and `ux_ergonomic_candidate_projection_profile_table.v1.json` free aesthetic variables. | Useful only if style variables repeatedly launder constraints or if fixtures cannot separate free variables from D-binding obligations. |
| `UxValidationSurfaceReport` | Separates semantic, entity, interaction, geometry, style/readability, and conformance findings. | Partly maps to `ux_morph_diagnostics.v1.json`, `ux_conformance_report.v1.json`, and ergonomic runtime bridge reports. | Good candidate for fixture/reporting slice. It should not replace existing diagnostics; it should decompose them for doctrine clarity. |

## 13. Relationship to existing ergonomics work

Ergonomic adjudication is not the whole of Morphic_ux. It is a sub-service and validation surface inside Morphic_ux.

The ergonomics schemas are especially relevant to:

- geometry and viewport envelopes;
- visibility and continuous visibility;
- targetability;
- typography and acuity;
- density;
- salience;
- screen size;
- component ergonomic classes;
- runtime measurement evidence;
- drift between adjudicated expectations and measured runtime.

They do not, by themselves, define all semantic supply, authority posture, interaction transformations, backend wiring, or UI entity grammar. For example, an ergonomic adjudication can say a send button is targetable and readable; it cannot alone prove that the send action is wired, that the button’s authority posture is correct, that dropdown state propagation is immediate, or that a backend semantic transformation succeeded.

The best architecture posture is:

> Ergonomics validates physical/readability/visibility feasibility inside a larger typed projection architecture.

## 14. Relationship to Morphic_ux frontend skill

`.agents/skills/morphic-ux-frontend` is the operational frontend delivery discipline. It tells implementers how to work:

- treat frontend work as projection, not styling;
- recover the UX bundle before coding;
- separate invariant and morphable choices;
- compile topology before visuals;
- preserve evidence-before-commit and authority boundaries;
- avoid visual authority inflation;
- use artifact-oriented design and support artifacts where repeated geometry/layout mechanics exist;
- keep source grounding visible through stable bindings and provenance hooks.

This architecture note sits upstream of that skill. It names the doctrine the skill is already gesturing toward: semantic supply, entity grammar, interaction transformations, geometry physics, and aesthetic variables as separate layers.

The skill’s references provide enforcement posture:

- `source-grounding.md` freezes the current reference family, authority policy, invariants, morph axes, topology, and same-context glossary.
- `artifact-oriented-design.md` prevents raw widget/pixel work from replacing typed artifact reasoning.
- `frontend-delivery-checklist.md` turns source grounding, invariant/morphable separation, and evidence/gate preservation into implementation checks.

A future checklist update should add explicit rows for semantic supply, entity grammar, interaction, geometry, style/readability, and validation-surface reporting.

## 15. V0 acceptance criteria

This note/framework is acceptable at v0 only if all of the following are true:

1. Existing repo artifacts are mapped accurately and conservatively.
2. The note does not claim that the current repo already implements the whole Morphic_ux architecture.
3. Visual screenshots/images are treated as evidence witnesses, not authority.
4. Geometry/physics is separated from style variables.
5. Backend semantic transformations are separated from UI entity behavior and visual layout.
6. Interaction behavior is separated from geometry and style.
7. Aesthetic variables are not confused with invariants.
8. Aesthetic variables become D-binding only through explicit authority elevation.
9. The Codex composer example is expressible as typed regions, relations, invariants, and validation surfaces.
10. Existing ergonomics work is positioned as a sub-service, not as the whole architecture.
11. Future schemas are framed as small additions or fixture extensions, not a monolithic rewrite.
12. The frontend skill remains the operational discipline; this note is doctrine and architecture, not a replacement skill.
13. Any future implementation slice can fail closed against repo source truth instead of relying on visual impression.
14. Any new schema proposal first demonstrates why fixture-level expression or existing schemas cannot express the requirement without ambiguity.
15. Any admitted new schema eventually carries rejection fixtures / negative cases.

## 16. Suggested next implementation slices

Keep the next work small and ordered. Slice E is conditional and should be blocked if Slice B/C can be expressed with existing schemas and fixtures.

| Slice | Description | Gate | Blocked / forbidden |
|---|---|---|---|
| Slice A | Promote this note only. | The note lands as doctrine/architecture; no runtime behavior changes; no new schemas; no rewritten app surfaces. | Any CSS, renderer, schema, or runtime work. |
| Slice B | Add a composer geometry fixture candidate with `composer_root`, `input_region`, `bottom_band_region`, `send_submit_region`, `option_menu_region`, `status_metadata_region`, and fullscreen/windowed/narrow assertions. | Fixture-level expression first; no runtime changes; must preserve the composer skeleton as geometry law, not style preference. | Creating `UxGeometryPhysicsProfile` before proving existing fixture/schema expression is ambiguous. |
| Slice C | Add a validation-surface report fixture that separates semantic/entity/interaction/geometry/style/conformance failures. | Must map to existing `ux_morph_diagnostics.v1.json`, `ux_conformance_report.v1.json`, and ergonomics reports where possible; should decompose, not replace. | Collapsing failures into generic UX findings; inventing broad diagnostics schema prematurely. |
| Slice D | Update `.agents/skills/morphic-ux-frontend/references/frontend-delivery-checklist.md` with five-layer validation rows and screenshot-as-witness reminder. | Checklist update only; should remain operational and source-grounded. | Treating the checklist as new architecture authority or changing app behavior. |
| Slice E | Only if needed, add a minimal geometry physics schema extension. | Conditional: allowed only after Slice B/C show current schemas cannot express composer geometry without ambiguity or repeated cross-surface need emerges. Requires positive and negative fixtures eventually. | Any monolithic `MorphicUxEverythingProfile`, renderer rewrite, generic design-system schema, or schema promotion because a concept is interesting. |

Do not begin with a broad runtime compiler rewrite. The repo already has meaningful governance, projection, ergonomics, diagnostics, conformance, and export substrate. The v0 path should add only the smallest missing objects needed to make geometry law and validation-surface separation explicit.

## 17. Open questions / risks

| Risk | Why it matters | Mitigation |
|---|---|---|
| Schema sprawl | The repo already has many governance and ergonomics schemas. A large new object universe would obscure rather than clarify. | Prefer fixture-level expression and small extensions. Only add schema when repeated cases cannot be represented or when existing schemas are ambiguous. |
| Overfitting to current UI prototype | The Morphic Studio prototype is visually rich but is not the production source of truth. | Treat prototypes as witnesses or inspiration unless bound by source-grounded fixtures. |
| Confusing screenshots with authority | Screenshots can make a surface look correct while violating semantic supply, authority, geometry, or source grounding. | Keep screenshots under E; require typed refs, fixtures, tests, and contracts for D claims. |
| Style variables laundering into constraints | Aesthetic preferences can accidentally hide evidence, authority distinctions, disabled states, or region relations. | Maintain an invariant ledger and elevate style variables only through explicit authority layers. |
| Geometry rules being underspecified | Without containment/docking/non-overlap/reflow laws, “fix the UI” degenerates into pixel patching. | Add a small composer geometry fixture first; add `UxGeometryPhysicsProfile` only if needed. |
| Not distinguishing possible data from wired data | A UI can imply capability that the backend does not actually supply. | Add semantic supply mapping only when current fixtures cannot express available/wired/authoritative/mutable/derived status clearly. |
| Mixing validation surfaces | A passing style screenshot can mask interaction, backend, geometry, or authority failures. | Report semantic, entity, interaction, geometry, style/readability, and conformance failures separately. |
| Treating ergonomics as the whole architecture | Targetability/readability are necessary but not sufficient for governed UX. | Keep ergonomics as a sub-service inside the broader Morphic_ux projection architecture. |
| Promoting schemas too early | A schema can become a new authority burden before there is enough cross-surface evidence. | Require fixture-first expression, repeated need or ambiguity proof, and eventual rejection fixtures. |

## Appendix A. Repo-grounded substrate ledger

Paths are relative to the repo root. This appendix preserves the repo grounding for the doctrine above. It is substrate evidence, not a standalone implementation plan.

| Existing repo artifact | Current role | Morphic_ux layer supported | Gap / note |
|---|---|---|---|
| `.agents/skills/morphic-ux-frontend/SKILL.md` | Operational frontend delivery skill. It explicitly treats frontend work as a projection problem, separates invariant/morphable decisions, requires topology compilation, evidence-before-commit, visible gates, stable bindings, and source grounding. | Cross-layer doctrine; entity grammar; interaction; projection; validation posture. | Skill guidance is operational, not a canonical architecture schema. It does not by itself define a geometry physics object family. |
| `.agents/skills/morphic-ux-frontend/references/source-grounding.md` | Frozen source map for the artifact-inspector reference family, approved profiles, authority policy, invariants, morph axes, topology, and same-context glossary. | Upstream authority; projection identity; invariants; validation. | Strong for the artifact-inspector family; not a general Morphic_ux layer model for all surfaces. |
| `.agents/skills/morphic-ux-frontend/references/frontend-delivery-checklist.md` | Delivery checklist for source stance, invariant/morphable separation, topology naming, evidence/gate visibility, stable IDs, and closeout. | Implementation discipline across all layers. | Should be extended later with explicit semantic/entity/geometry/style validation-surface checks. |
| `.agents/skills/morphic-ux-frontend/references/artifact-oriented-design.md` | Defines surface artifacts and support artifacts such as layout solvers, pane ratio engines, docking helpers, text measurement, and diff engines. | UI entity grammar; geometry/physics; operational artifact boundaries. | Provides doctrine for geometry support artifacts but no minimal Morphic_ux geometry profile schema. |
| `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_PROTOCOL_v0.md` | Support draft for enacting the frontend skill, distinguishing skill gaps from tool gaps, logging recurring burdens, and preventing silent compensation. | Validation posture; support/tool discovery. | It explicitly does not authorize runtime/tool/schema changes by itself. |
| `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_TASK_CORPUS_v0.md` | Task corpus for repeated governed enactment around conformance review, alternate profile morphs, gated interactions, responsive evidence reachability, state distinctions, and unlawful proposal diagnosis. | Validation; interactions; evidence reachability. | It is a task corpus, not a layer architecture. |
| `docs/templates/MORPHIC_UX_GOVERNED_ENACTMENT_BURDEN_LOG_TEMPLATE_v0.md` | Template for recording recurring burden classes, candidate support surfaces, and promotion decisions. | Validation and future tooling evidence. | Useful for deciding whether a geometry/profile artifact deserves promotion; not itself a UX schema. |
| `packages/adeu_core_ir/schema/ux_domain_packet.v1.json` | Captures reference identity, approved profile, user archetype, device class, environment assumptions, risk, trust sensitivity, interaction mode, tasks, evidence visibility, utility ranking, authority policy, and supporting artifacts. | Upstream capability/data; utility posture; authority boundary. | Does not yet model a first-class map of actual wired data/actions with authoritative/mutable/derived status. |
| `packages/adeu_core_ir/schema/ux_morph_ir.v1.json` | Captures ontology, epistemics, deontics, utility, invariants, morphable surface choices, morph axes, surface compilation units, regions, actions, artifacts, evidence packets, trust lanes, and state vocabulary. | UI entity grammar; invariant ledger; morph profile. | Strong governance vocabulary, but not a full reusable UI grammar for inputs, dropdowns, popups, badges, tabs, checkmarks, or composer regions. |
| `packages/adeu_core_ir/schema/ux_interaction_contract.v1.json` | Captures surface events, UI transitions, preconditions, visible consequences, runtime effects, reversibility, confirmation, evidence, rollback, failure/success surfaces, gates, and bindings. | Interaction / transformations. | Current enumerations are tuned to the artifact-inspector family. Generic click/select/close/focus/hover/resize and outside-click/dropdown obligations need extension or fixture-level expression. |
| `packages/adeu_core_ir/schema/ux_surface_projection.v1.json` | Captures surface root, bounded workbench, responsive behaviors, regions, lanes, action clusters, state surfaces, evidence-before-commit, stable provenance hooks, and observable bindings. | UI entity grammar; spatial projection skeleton; evidence reachability. | It names regions/lanes and responsive doctrine, but it does not yet provide precise geometry physics laws such as containment, docking, overlay, adjacency, non-overlap, or fullscreen/windowed composer invariants. |
| `packages/adeu_core_ir/schema/ux_surface_compiler_export.v1.json` | Captures implementation target payloads, binding maps, gating diagnostics, conformance snapshots, CSS token maps, and derivation metadata. | Projection export; style token boundary; validation. | Useful for downstream style tokens, but not a geometry authority and not a runtime proof. |
| `packages/adeu_core_ir/schema/ux_surface_compiler_variant_manifest.v1.json` | Captures profile variants, exported artifact refs, source hashes, and conformance gates. | Projection variants. | Good for approved profile variants; not a complete Morphic_ux projection profile object. |
| `packages/adeu_core_ir/schema/ux_morph_diagnostics.v1.json` | Captures violation findings, severity, provenance pointers, rendered surface assertion inputs, evidence refs, and conformance impact. | Validation/conformance. | Existing violation families are valuable but do not yet separate semantic, entity, geometry, and style failures as first-class validation surfaces. |
| `packages/adeu_core_ir/schema/ux_conformance_report.v1.json` | Captures conformance judgment, severity counts, failed/warning families, supporting finding IDs, and canonical derivation metadata. | Conformance/reporting. | Aggregates governance outcome; should remain separate from lower-level backend/entity/geometry/style test surfaces. |
| `packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json` | Captures component semantic kind, ergonomic class, visibility state, collapse policy, continuous visibility, and reveal transition. | Entity grammar; visibility; ergonomics. | Useful bridge to entity/geometry validation; not a full grammar or physics model. |
| `packages/adeu_core_ir/schema/ux_component_ergonomic_registry.v1.json` | Captures ergonomic classes, targetability, readability, default visibility, collapse policy, and rule bindings. | Ergonomics; entity classification; geometry constraints. | Ergonomic classes are a sub-service inside Morphic_ux, not the whole architecture. |
| `packages/adeu_core_ir/schema/ux_ergonomic_case_envelope.v1.json` | Captures viewport, available geometry, DPR/PPI, zoom, viewing distance, minimums, provenance, admissibility, input mode, and window occupancy mode. | Geometry/physics evidence; ergonomic measurement. | Strong for measured constraints; not a general region-law schema. |
| `packages/adeu_core_ir/schema/ux_ergonomic_rule_authority_stack.v1.json` | Captures authority-layered ergonomic rules: constitutional surface invariants, repo policy, external floors, platform presets, user preferences, and heuristic utility. | D-binding ergonomic authority; style/geometry floors. | Provides authority elevation pattern for variables, but only inside ergonomics. |
| `packages/adeu_core_ir/schema/ux_ergonomic_candidate_projection_profile_table.v1.json` | Captures candidate projection profiles, target envelopes, region/lane/action refs, same-context reveal terms, visibility claims, target claims, and declared free aesthetic variables. | Geometry/visibility candidate projection; aesthetic variable declaration. | Good starting point for separating free aesthetic variables from D-binding constraints. It still does not encode full composer-region physics. |
| `packages/adeu_core_ir/schema/ux_ergonomic_adjudication_request.v1.json` and `ux_ergonomic_adjudication_result.v1.json` | Capture ergonomic adjudication inputs and outcomes, including feasible/blocked/ambiguous measurement obligations. | Ergonomic validation surface. | Adjudication is not the whole Morphic_ux doctrine; it validates a subset. |
| `packages/adeu_core_ir/schema/ux_ergonomic_runtime_measurement_evidence.v1.json` and `ux_ergonomic_runtime_bridge_report.v1.json` | Capture measured runtime geometry/visibility/typography and bridge drift against adjudicated expectations. | Geometry/readability runtime evidence. | Valuable for runtime witness evidence; should not be confused with semantic supply or interaction behavior validation. |
| `spec/ux_*.schema.json` | Mirrored exported schema specs for UX governance and ergonomics schemas. | Schema publication/export. | Export tests assert byte-identical mirrors; the authoritative schema source remains under `packages/adeu_core_ir/schema/`. |
| `apps/api/fixtures/ux_governance/vnext_plus61/` | Reference domain packet, morph IR, first approved profile table, and same-context reachability glossary for the artifact-inspector family. | Upstream/domain; morph axes; invariants; source-grounded profiles. | Concrete reference family, not a universal UI doctrine. |
| `apps/api/fixtures/ux_governance/vnext_plus62/` | Reference interaction contract and surface projection. | Interaction; projection; regions/lanes/action/state/evidence. | Strong current reference for governed projection, but not composer geometry. |
| `apps/api/fixtures/ux_governance/vnext_plus63/` | Rendered reference surface contract with truth source policy and required binding/provenance exposures. | Runtime projection witness; source-grounded rendered contract. | Important witness/contract, but not visual screenshot authority. |
| `apps/api/fixtures/ux_governance/vnext_plus64/` | Diagnostics and conformance report for the reference profile. | Conformance/reporting. | Useful seeded violation families; not decomposed into all validation surfaces requested here. |
| `apps/api/fixtures/ux_governance/vnext_plus65/` | Alternate/reference compiler exports, alternate diagnostics/conformance, and variant manifest. | Variant projection/export. | Demonstrates profile variants and CSS token export; not a general geometry physics model. |
| `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py` and `test_ux_ergonomics_export_schema.py` | Assert deterministic export/mirroring of schemas into `spec/`. | Schema governance. | Export identity tests do not validate UX behavior. |
| `packages/adeu_core_ir/tests/test_ux_governance.py`, `test_ux_governance_v36b.py`, `test_ux_governance_v36d.py`, `test_ux_governance_v36e.py`, `test_ux_governance_evidence.py` | Validate binding, profile identity, glossary freezing, projection/interaction coupling, gate sources, conformance derivation, compiler export gates, and fail-closed evidence posture. | Cross-layer governance validation. | Strong current test substrate; not a complete set of backend/entity/geometry/style tests. |
| `packages/adeu_core_ir/tests/test_ux_ergonomics.py`, `test_ux_ergonomics_admissibility.py`, `test_ux_ergonomic_adjudication.py`, `test_ux_ergonomic_runtime_bridge.py` | Validate ergonomics schemas, visibility contracts, candidate profile binding, admissibility, adjudication, runtime measurement, and bridge drift. | Ergonomic geometry/visibility/readability validation. | Ergonomics tests should remain a sub-surface of Morphic_ux validation, not the whole architecture. |
| `packages/adeu_core_ir/src/adeu_core_ir/ux_governance.py` | Source-level governance constants and validators for frozen families, profiles, morph axes, epistemic states, same-context terms, authority policy, widget semantic token warnings, and evidence checks. | Governance authority and validation. | Good authority substrate; not a UI runtime. |
| `apps/web/src/app/artifact-inspector/reference-surface.ts` and `apps/gptpro-codex-workbench/src/app/artifact-inspector/reference-surface.ts` | Load and bind the v61-v63 fixture bundle; assert shared identity, profile, authority boundary, same-context glossary, route-change prohibition, exposure targets, lane/cluster mapping, target index, bindings, and provenance. | Rendered projection contract and binding bridge. | Artifact-inspector-specific implementation anchor. |
| `apps/web/src/app/artifact-inspector/page.tsx` and `apps/web/src/app/artifact-inspector/page.module.css` plus mirrored `apps/gptpro-codex-workbench` versions | Render the reference workbench with regions, lanes, evidence/status surfaces, action clusters, and data attributes. CSS defines grid and responsive behavior. | Realized reference surface; projection witness. | A current implementation example, not a generalized geometry law. |
| `apps/web/prototypes/adeu-studio-morphic-surface.jsx`, `apps/gptpro-codex-workbench/prototypes/adeu-studio-morphic-surface.jsx`, `apps/web/src/app/morphic-studio/page.jsx`, `apps/gptpro-codex-workbench/src/app/morphic-studio/page.jsx` | Cinematic/prototype Morphic Studio surfaces using O/E/D/U language, semantic lattice, and governed overlays. | Conceptual/prototype witness. | The frontend skill explicitly treats the prototype as philosophical inspiration unless separately grounded. |
| `apps/gptpro-codex-workbench/src/app/codex-workbench/codex-workbench-client.tsx` and `apps/gptpro-codex-workbench/src/app/codex-workbench/page.module.css` | Current Codex workbench composer surface with prompt entry, context buttons, send action, metadata, and responsive CSS. | Running example substrate: input/action/status regions. | Existing app surface does not currently expose a first-class Morphic_ux composer-region geometry profile. |
| `apps/codex-review-shell/src/renderer/codex-surface.html`, `codex-surface.css`, `codex-surface.js` | Composer shell with control row, textarea, submit button, and responsive composer CSS; JavaScript queues local notes. | Running example substrate: bottom band and submit relation. | Useful witness for composer anatomy, not authority for the architecture by itself. |
| `apps/opus-codex-workbench/src/components/conversation.js` and `apps/opus-codex-workbench/src/styles/conversation.css` | Transcript + composer implementation with textarea, send button, toolbar toggles, auto-resize, active context tab state, and composer bottom band styling. | Running example substrate: entity behavior and bottom-band structure. | Shows existing behavior patterns but not a typed geometry/interaction contract. |
| `apps/gpt54-codex-workbench/src/renderer/app.ts` and `apps/gpt54-codex-workbench/src/renderer/styles.css` | Additional Codex-style composer implementation with textarea, artifact buttons, hint, send action, and responsive footer layout. | Running example substrate. | Same gap: no first-class Morphic_ux composer projection fixture. |
| `packages/adeu_agentic_de/schema/agentic_de_morph_ir.v1.json`, `agentic_de_interaction_contract.v1.json`, `agentic_de_surface_authority_descriptor.v1.json`, `agentic_de_repo_writable_surface_descriptor.v1.json`, `agentic_de_repo_write_surface_admission_record.v1.json`, `agentic_de_repo_writable_surface_hardening_register.v1.json` | Adjacent agentic surface authority and repo-writable-surface governance. | Authority analogy; upstream capability/action boundary when UX surfaces touch writable behavior. | Relevant only by analogy unless a UI projection controls agentic write/execute surfaces. |
````

## 2. Changelog from baseline

* Added a compact **Morphic_ux v0 laws** block near the top.
* Added the **Projection lifecycle** from semantic supply through conformance/admission.
* Added explicit **Non-goals** to prevent design-system, renderer, screenshot-authority, and schema-universe overreach.
* Moved the detailed repo map into **Appendix A** and added a short body/appendix distinction.
* Strengthened the **schema admission rule**: fixture-level expression first, no interesting-concept schemas, no `MorphicUxEverythingProfile`, small typed additions only, eventual negative fixtures.
* Added the **minimal composer geometry fixture skeleton** with fullscreen/windowed/narrow viewports and region assertions.
* Tightened the **Codex composer** example around geometry law rather than visual repair.
* Reworked next slices into **Slice A-E gates**, with Slice E explicitly conditional and blocked if Slice B/C can use existing schemas.
* Preserved the five-layer model, ODEU interpretation, invariant split, validation surfaces, ergonomics-as-sub-service posture, and frontend skill relationship.

## 3. Do not implement yet

* Do not create `MorphicUxEverythingProfile`.
* Do not create `UxGeometryPhysicsProfile` until the composer fixture cannot be expressed with existing schemas/fixtures.
* Do not create a broad `UxEntityGrammarRegistry` or design-system schema.
* Do not create `UxSemanticSupplyMap` unless repeated surfaces need it or current fixtures are ambiguous.
* Do not create `UxAestheticVariableSet` unless style-variable laundering appears repeatedly and cannot be handled by existing fixtures.
* Do not rewrite renderers, compilers, CSS systems, or Codex composer runtime behavior in this pass.
* Do not treat screenshots/images as authority.
* Do not replace existing diagnostics/conformance schemas with a new validation universe.
