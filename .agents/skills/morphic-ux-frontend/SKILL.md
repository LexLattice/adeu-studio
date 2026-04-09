---
name: morphic-ux-frontend
description: "Use when designing, reviewing, or implementing ADEU-style frontend surfaces that must follow Morphic UX doctrine: lawful morph selection, evidence-before-commit visibility, explicit authority boundaries, truthful state rendering, and region/lane/action topology derived from UX artifacts instead of free-form UI improvisation."
---

# Morphic UX Frontend

Treat frontend work as a projection problem, not a styling problem.

The surface is allowed to morph. The governing machine is not.

Use this skill for operator workbenches, evidence-sensitive views, bounded review surfaces, artifact inspectors, and other interfaces where authority, evidence, and state truth must remain explicit. Do not use it for generic marketing pages or style-only polish passes with no governed interaction model.

## Quick start

1. Read the nearest UX source artifacts and inspect the current implementation surface before touching layout.
2. Separate invariant rules from morphable choices.
3. Choose or infer a lawful morph profile.
4. Compile the surface topology in this order:
   - regions
   - lanes
   - action clusters
   - state surfaces
   - explicit commit or handoff boundary
5. Implement visuals that express posture, evidence, and state truth without inflating authority.
6. Verify that required evidence remains same-context reachable before any commit or destructive step.

If the repo already contains released UX artifacts, treat them as authoritative input. Do not replace them with fresh UI heuristics.

Read [references/source-grounding.md](references/source-grounding.md) for the repo's current morphic reference family and source files.
Read [references/frontend-delivery-checklist.md](references/frontend-delivery-checklist.md) when implementing or reviewing a concrete surface.
Read [references/artifact-oriented-design.md](references/artifact-oriented-design.md) when deciding whether a needed capability should be imported, wrapped, normalized, or built as a reusable artifact.
For support-layer tool discovery by governed enactment, also use:
- `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_PROTOCOL_v0.md`
- `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_TASK_CORPUS_v0.md`
- `docs/templates/MORPHIC_UX_GOVERNED_ENACTMENT_BURDEN_LOG_TEMPLATE_v0.md`

## Run stance

Before substantive work, declare all four:

- `task_mode`
  - `design`
  - `implementation`
  - `review`
- `execution_mode`
  - `standard`
  - `governed_enactment`
- `grounding_status`
  - `repo_grounded`
  - `artifact_grounded_repo_incomplete`
  - `inference_only`
- `implementation_inspection_status`
  - `implementation_inspected`
  - `implementation_not_inspected`

If required UX artifacts, implementation facts, or runtime facts are missing, mark the
surface judgment as inferred rather than speaking in repo-native certainty.

## Operational doctrine

These directives are non-negotiable.

- No free-form UI codegen without IR or an explicit equivalent design brief.
- UI artifacts may express authority, but may not mint authority.
- Treat the artifact as the minimal operative unit of meaning. Do not reason at raw widget,
  pixel, or repeated hand-calculation level when a stable artifact boundary can exist.
- Unknown or uninspected implementation facts must remain marked as inferred. Do not counterfeit repo-grounded certainty.
- Do not create visual authority inflation. Provisional, advisory, ambiguous, and authoritative states must look materially different.
- `validated` is not `authoritative`, and unknown state is not success.
- Required evidence must be visible or same-context reachable before commit.
- Primary action posture must stay unambiguous.
- Advisory actions and authoritative or commit actions must remain distinct.
- State transitions must be observable in the surface.
- If a gated action exists, its disabled or unavailable state should usually remain visible so the operator can understand what is missing.
- When provenance and conformance matter, expose stable bindings or hooks for authority-bearing controls, evidence-bearing regions, and state-distinction surfaces.
- Projection may change arrangement, disclosure style, and component topology within bounds. Projection may not change the governing meaning of the surface.

## Workflow

### 1. Build or recover the UX bundle and inspect the realized surface

Before writing components, recover or infer the smallest useful bundle:

- `ux_domain_packet`
  - task set
  - risk level
  - trust sensitivity
  - utility ranking
  - evidence visibility requirements
- `ux_morph_ir`
  - invariants
  - morph axes
  - ontology
  - epistemic and deontic rules
- `ux_surface_projection`
  - regions
  - lanes
  - action clusters
  - state surfaces
  - responsive behavior
- `ux_interaction_contract`
  - events
  - preconditions
  - visible consequences
  - gate sources
  - rollback and failure surfaces

For live frontend tasks, also inspect the currently realized surface before proposing
change:

- route entrypoint or page surface
- component tree or region composition
- state-bearing surfaces
- interaction and commit boundaries
- evidence-bearing regions and responsive behavior when reachable

If these artifacts do not exist yet, write a compact design note in that shape before implementation. Do not skip directly from user prose to JSX.
If implementation inspection does not happen, say so explicitly and keep any surface judgment at inferred posture.

### 2. Separate invariant from morphable

Write down both lists explicitly.

Invariant examples:

- evidence before commit visibility
- destructive action gating
- trust boundary clarity
- observable state transitions
- unambiguous primary action

Morphable examples:

- split pane vs hub and spoke
- disclosure style
- navigation placement
- exact component topology inside a bounded lane

This is the central Morphic UX move: lawful variability, not aesthetic entropy.

### 3. Select a morph profile

Choose morph axes deliberately. If the family already has approved profiles, stay inside them unless the task explicitly expands the contract.

Current repo-native axes:

- `density`
- `navigation_mode`
- `information_posture`
- `interaction_tempo`
- `salience_posture`
- `state_exposure`
- `command_posture`

Interpret them operationally:

- `density`: how much information is shown at once
- `navigation_mode`: whether the surface preserves simultaneous context or pivots between hubs
- `information_posture`: whether evidence, tasks, or summary leads
- `interaction_tempo`: whether the surface optimizes for guided progression or expert speed
- `salience_posture`: which classes of information dominate visually
- `state_exposure`: how explicitly the surface renders status and intermediate truth
- `command_posture`: whether action lanes separate safe and commit paths

If risk is high and trust is authority-sensitive, bias toward evidence-first, full-explicit state rendering, and dual-lane command posture.

### 4. Compile topology before components

Work from structural roles, not widget names.

Preferred compilation order:

1. Define the bounded workbench root.
2. Define regions by responsibility.
3. Define lanes inside regions.
4. Attach action clusters to lanes.
5. Attach state surfaces to lanes.
6. Mark evidence-bearing regions and trust-boundary surfaces.
7. Mark the explicit commit or handoff boundary.

Use widget choices such as tabs, drawers, tables, cards, accordions, and modals only after the role topology is stable. Do not let widget preference drive the governance model.

### 5. Work artifact-first, not trial-and-error first

Treat the artifact as the minimal operative unit of meaning.

If a needed capability already exists as a trustworthy artifact, import and align it.
If it does not, build it once as an artifact rather than repeatedly reconstructing it
in human reasoning or ad hoc UI code.

For this skill, an artifact may be:

- a surface artifact:
  - terminal
  - editor
  - diff viewer
  - tree view
  - file picker
  - log viewer
- a support artifact:
  - layout solver
  - constraint or geometry solver
  - pane ratio engine
  - geometric neighboring or packing helper
  - docking or split-view engine
  - text measurement helper
  - diff or merge computation engine

If the same abstract function keeps reappearing, do not keep re-deriving it manually in
every design pass. Push it down into a reusable artifact and operate at the higher-level
formula instead.

For support artifacts specifically, the host should name the relation it wants to hold:

- target ratios
- adjacency rules
- non-overlap constraints
- minimum readable widths
- docking or preservation priorities

The support artifact should own the repeatable math or mechanics that realize those
relations.

Bad pattern:

- repeatedly reasoning spacing, ratios, collision avoidance, or pane neighboring through
  trial and error in the main design loop

Better pattern:

- define the intended relation at the UX level
- use or build one artifact that solves the repeated lower-level math or mechanics

### 6. Prefer adopting or composing bounded artifacts before rebuilding capability

Do not assume every needed capability should be built from scratch.

If a mature OSS implementation already solves a bounded problem such as:

- terminal
- editor
- diff viewer
- tree view
- file picker
- log viewer
- layout solver
- docking engine
- geometry helper

then default to adopting it as a bounded artifact unless the task requires novel core
semantics or constraint behavior that the existing implementation cannot support.

The key rule is:

- reuse implementation substrate freely;
- do not outsource Morphic UX law to the imported module.

Treat the external implementation as a capability-bearing sub-surface inside a governed
host workbench.

That means the host surface still owns:

- region and lane placement
- authority posture
- evidence-before-commit behavior
- state truth rendering
- bindings and provenance hooks where needed
- action gating and surrounding commit semantics

Normal integration order:

1. name the required artifact and its meta-properties
2. decide whether an existing artifact can be imported and aligned
3. if no single artifact fits, decide whether several lower-level artifacts can be composed into one bounded local artifact
4. if yes, classify the adopted or composed artifact's role in the workbench
5. decide which semantics remain internal to the artifact and which must be normalized by the host
6. wrap or adapt its events and state into the local interaction contract
7. normalize visual posture if the artifact overstates authority, success, or completion
8. expose stable bindings, hooks, or test anchors if the surrounding surface requires conformance visibility
9. if no acceptable artifact exists, build one reusable artifact rather than repeatedly solving the same problem inline

Examples:

- a terminal can be adopted as the execution substrate for one lane, but the host still
  decides whether that lane is advisory, operational, diagnostic, or commit-adjacent
- an editor can be adopted as a text substrate, but the host still renders authoritative
  versus provisional state and governs save or commit posture
- a layout or geometry helper can be adopted or built as a support artifact so the
  surface can specify desired ratios, adjacency, or non-overlap rules without manually
  re-solving the math every iteration
- if no existing layout helper fits, compose one bounded local artifact around the
  chosen constraint inputs instead of scattering ratio math across unrelated components

Failure modes to avoid:

- treating raw widgets or pixel values as the primary design unit when an artifact
  boundary should exist
- letting a vendor component dictate the lane topology
- inheriting a foreign command grammar that contradicts the chosen morph profile
- accepting success, warning, or authority styling from the imported module without checking whether it matches the host truth posture
- placing critical evidence or trust-boundary semantics inside a black-box submodule with no surrounding host explanation
- repeatedly using human trial-and-error to recover the same geometric or proportional schema when that schema should already exist as an artifact
- importing a helper that optimizes low-level layout while silently breaking the host's evidence, trust, or command-posture law

### 7. Render truth, posture, and reachability

The surface must make these things legible at a glance:

- what is advisory
- what is authoritative
- what is provisional
- what is ambiguous or conflicted
- where required evidence lives
- where the commit boundary begins
- what changed and what remains read-only

Minimum epistemic distinctions to preserve:

- `loading`: never render as absence
- `draft` or `candidate`: marked as provisional
- `validated`: visibly better than draft, but still not authoritative
- `authoritative`: materially distinct from every provisional state
- `conflicted`, `stale`, or `ambiguous`: never styled as success

Useful patterns:

- separate advisory action clusters from commit clusters physically, not just by button label
- give warning, diagnostic, provisional, and authoritative states distinct surfaces or markers
- keep evidence lanes persistent or same-context reachable
- keep the commit gate explicit, labeled, and visually later than analysis and evidence review
- render gate sources or prerequisite explanations near gated controls when possible

Forbidden patterns:

- single-click irreversible commit
- success styling on unknown or ambiguous state
- hidden evidence behind route change when evidence is required before commit
- collapsing advisory and authoritative material into one undifferentiated control block
- decorative intensity that implies greater truth, confidence, or permission than the system actually has

### 8. Implement responsive morphs without breaking the doctrine

Responsive adaptation should preserve governed reachability.

- Stacking regions on narrow viewports is acceptable.
- Reordering regions is acceptable if evidence and status stay reachable before commit.
- Replacing same-context evidence with a route transition is not acceptable unless the contract changes.
- Keep trust and diagnostic surfaces present on mobile, even if disclosure becomes progressive.

The repo's current reference surface keeps the same workbench context while moving from a three-column layout to two columns and then one column. That is the right kind of morph: spatial adaptation without semantic breakage.

### 9. Governed enactment discipline

When `execution_mode` is `governed_enactment`, do not silently compensate for missing
support surfaces with extra hidden reasoning.

If you repeatedly have to reconstruct or simulate:

- layout or region topology
- authority posture
- evidence reachability
- morph-profile conformance
- binding or provenance coverage
- stable layout or geometry math

then log that as a burden instead of silently absorbing it.

For each recurring burden, extract a minimal candidate support surface with:

- the burden being externalized
- the desired function or operation
- why this should be a tool or artifact rather than more prose
- classification:
  - `lawful_required`
  - `reliable_required`
  - `performance_only`
  - `skill_gap`

Use:

- `docs/support/DRAFT_MORPHIC_UX_GOVERNED_ENACTMENT_PROTOCOL_v0.md`
- `docs/templates/MORPHIC_UX_GOVERNED_ENACTMENT_BURDEN_LOG_TEMPLATE_v0.md`

### 10. Verify before closing

Check all of the following:

- Does the surface still match the chosen morph axes?
- Are invariants preserved?
- Can the operator reach required evidence before any commit or destructive step?
- Are advisory and authoritative actions visually and spatially distinct?
- Are authoritative, provisional, stale, conflicted, and ambiguous states distinguishable?
- Does the UI describe authority instead of creating it?
- Do responsive states preserve the same-context rule or make any break explicit?
- If an OSS or external sub-module was adopted, does the host still own the governing semantics rather than deferring them to the imported implementation?
- If repeated geometric, proportional, or neighboring logic was needed, was it externalized into a reusable artifact instead of being re-derived inline?

For reviews, classify issues with this threshold:

- `fail`: required evidence not same-context reachable, advisory and authoritative material visually collapsed, destructive action lacks confirmation, or one region presents competing primary actions
- `needs_review`: provisional data styled as authoritative, failure mode lacks visible recovery path, or the realized command grammar drifts from the chosen morph profile

## Design guidance

Use strong visual hierarchy, but make it answer the contract.

- Favor dense, operational layouts when the archetype is an expert operator.
- Use calm but high-contrast tokens for evidence, warning, advisory, and authority posture.
- Put labels, badges, and boundary markers on structures that matter, not everywhere.
- Prefer persistent panels, split panes, and bounded workbench sections over modal churn when analysis requires simultaneous context.
- Motion should reveal state change or focus shift. Avoid cinematic motion that performs confidence rather than explaining system state.
- If using a more expressive visual language, treat the prototype in `apps/web/prototypes/adeu-studio-morphic-surface.jsx` as philosophical inspiration only. Do not copy its theatrical presentation into production workflow surfaces unless the user explicitly asks for that mode.

## Output shape

When using this skill for a fresh frontend task, produce these artifacts in your reasoning or implementation notes:

- run stance declaration
- selected or inferred UX bundle
- implementation inspection note
- invariant list
- morphable list
- chosen morph axes
- artifact inventory with import, compose, or build decisions
- region and lane map
- evidence-before-commit plan
- authority boundary plan
- state rendering plan
- responsive preservation plan

If `execution_mode` is `governed_enactment`, also produce:

- burden log summary
- candidate support-surface summary
- explicit `tool_gap` versus `skill_gap` judgment

If the task is a review, report findings against those same categories.
