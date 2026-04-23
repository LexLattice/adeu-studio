# 1. Executive judgment

**Run posture:** `task_mode=design`; `execution_mode=standard`; `grounding_status=repo_grounded`; `implementation_inspection_status=implementation_not_inspected` because this is a v0 architecture note, not a route-level implementation review.

The better subsystem name is **Ergonomic Instantiation Adjudicator**. The original intuition, “ergonomic visual calculator” / “ergonomic surface adjudicator,” is right, but the decisive word is **instantiation**: the subsystem adjudicates how a stable Morphic UX surface may lawfully become concrete under a specific human + device + task envelope.

The subsystem should not be a design assistant. It should be a **bounded, deterministic-or-nearly-deterministic adjudication layer** that takes:

```text
constitutional surface law
+ case envelope
+ component visibility contract
+ candidate morphs/projections
```

and emits:

```text
instantiated invariant ranges
+ blocked configurations with reason codes
+ preferred projection hints
+ ambiguity/confidence markers
+ implementation measurement obligations
```

The central separation must be schema-enforced:

```text
constitutional invariants
  = sameness law of the UI object

instantiated invariants
  = concrete case-specific constraints required for this user/screen/task

free aesthetic variables
  = cheap later iteration space, unless they encode authority, evidence, or legibility
```

This belongs naturally as a sibling extension to the existing `ux_domain_packet@1 → ux_morph_ir@1 → ux_surface_projection@1 → ux_interaction_contract@1 → ux_morph_diagnostics@1 → ux_conformance_report@1` family, not as a replacement for it.

# 2. Why this subsystem is load-bearing for mature Morphic_ux

The current Morphic UX doctrine already has the correct constitutional spine: UI is a projection problem, not a styling problem; the governing machine must remain stable while the surface may morph; evidence, authority, state truth, gates, lanes, and region topology are prior to widget taste. The existing repo family expresses this through `ux_domain_packet@1`, `ux_morph_ir@1`, `ux_surface_projection@1`, `ux_interaction_contract@1`, diagnostics, conformance, and compiler export. That stack can say **what must remain true** across morphs.

The missing layer is the one that says **what becomes concretely justified here**.

A lawful surface object can be semantically stable while still requiring different instantiated invariants when the same object is shown:

```text
on a 27-inch monitor at 70 cm
vs. a 13-inch laptop half-screen
vs. a quarter-screen floating inspector
vs. touch-first tablet use
vs. lower-acuity long-read posture
vs. high-risk commit posture with evidence-before-commit obligations
```

Generic responsive design mostly answers: “what CSS/layout changes when the viewport changes?” Modern platform mechanisms such as media queries, container queries, `pointer` / `any-pointer`, `hover`, and viewport APIs are useful substrate, but they do not know the Morphic UX object, its trust boundary, its evidence law, or its component visibility contract. Media queries expose device and environment features, and container queries allow styles based on container size, but neither decides which evidence lane must remain same-context reachable before commit. ([MDN Web Docs ][1])

Accessibility standards are necessary but insufficient. WCAG 2.2 gives important testable floors: target-size minimums, contrast requirements, reflow, resize-text, non-text contrast, text-spacing, and related criteria. Those are substrate constraints, not a complete answer to “how should this ADEU surface instantiate its lanes, columns, density, and collapse law under this case envelope?” WCAG itself says the guidelines cover a wide range of needs but do not address every user need; WCAG success criteria are technology-independent and are intended to be testable, not to encode a whole Morphic UX governance model. ([W3C][2])

The load-bearing move is therefore:

```text
ux_morph_ir@1
  = constitutional law / allowed morph grammar

ux_ergonomic_adjudication_result@1
  = case-specific instantiation law / admissible range of concrete projection
```

In O/E/D/U terms:

| Axis           | Role in this subsystem                                                                                                                                       |
| -------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **Ontology**   | Defines user envelope, display envelope, task posture, component classes, surface regions, lanes, candidate projections.                                     |
| **Epistemics** | Records what is measured, declared, inferred, uncertain, or merely heuristic; binds outputs to source artifacts and measurement provenance.                  |
| **Deontics**   | Blocks configurations that violate constitutional invariants, accessibility floors, evidence-before-commit, targetability, or declared visibility contracts. |
| **Utility**    | Ranks feasible projections by task fit, operator speed, error prevention, monitoring continuity, density economy, and comfort.                               |

# 3. Existing tool/standards landscape and what to reuse

## 3.1 Accessibility standards: use as floors, not as the whole solver

**WCAG 2.2** should be the primary standards substrate for web surfaces. It gives specific constraints that can become rulebook entries: ordinary text contrast of at least 4.5:1, large-text contrast of at least 3:1, AAA enhanced contrast of 7:1, text resize to 200% without loss of content/functionality, reflow at 320 CSS px for vertical scrolling content, and non-text/UI component contrast of at least 3:1. ([W3C][2])

**Target size** should be treated as a major v0 constraint family. WCAG 2.2 SC 2.5.8 sets a Level AA pointer target minimum of 24 by 24 CSS px, with spacing and other exceptions; SC 2.5.5 sets an enhanced 44 by 44 CSS px target floor for pointer inputs, with exceptions. These should be imported as minimum legal floors, while the adjudicator may select higher floors for touch, destructive actions, high-frequency controls, tremor risk, or low-confidence motor envelopes. ([W3C][3])

**Text spacing and long-read presentation** should be used as legibility guardrails. WCAG text spacing requires no loss of content/functionality when line height, paragraph spacing, letter spacing, and word spacing are adjusted to specified values; WCAG visual-presentation guidance also names constraints such as line width not exceeding 80 characters or glyphs for blocks of text. These are useful for long-read and evidence-review postures, but they do not decide region topology. ([W3C][4])

## 3.2 Platform hit-target guidance: use as input-mode presets

Platform guidelines should not override Morphic UX law, but they are good preset sources. Apple advises hit targets of at least 44×44 points and text of at least 11 points at typical viewing distance; Android accessibility guidance recommends touch targets of at least 48×48 dp, separated by 8 dp or more, and notes that 48×48 dp is about 9 mm; Microsoft’s Windows targeting guidance gives a 7.5 mm / 40×40 px touch target rule of thumb on a 135 PPI display. ([Apple Developer][5])

V0 reuse role:

```text
mouse/fine pointer     -> WCAG AA floor + component/risk inflation
touch/coarse pointer   -> platform floor preset, usually >= 40–48 effective px/dp class
pen                    -> between mouse and touch, but high-precision actions still need spacing
hybrid                 -> choose the stricter active input mode, or expose mode-specific variants
destructive/commit     -> always inflate target/spacing and require gate visibility
```

## 3.3 Display, viewport, and measurement substrate

The adjudicator needs an **envelope collector**, not a generic responsive engine. Browser/platform data sources include:

```text
window / visual viewport
devicePixelRatio
ResizeObserver
CSS media features: pointer, any-pointer, hover, any-hover, prefers-contrast, forced-colors
CSS container queries
element bounding boxes
computed font sizes and line boxes
```

`devicePixelRatio` gives the ratio of physical pixels to CSS pixels, but MDN notes it is not Baseline because it does not work in all widely used browsers; v0 should therefore treat physical-size inference as confidence-bearing rather than absolute. ResizeObserver is well-established for monitoring element size changes, and VisualViewport represents the visual viewport for a window. ([MDN Web Docs ][6])

Reuse role:

```text
browser APIs       -> collect runtime envelope and measured implementation facts
container queries  -> implement already-adjudicated morph thresholds
ResizeObserver     -> detect envelope transitions and produce measurement evidence
Playwright         -> replay cases and extract bounding boxes / computed styles
```

## 3.4 Ergonomics and human-factors models

Human-factors sources should be used as **calibrated heuristics with explicit uncertainty**, not as medical truth. OSHA’s workstation guidance gives a common monitor viewing distance range of 20–40 inches / 50–100 cm and notes that text size may need to increase for smaller monitors. Fitts’s Law is useful because target acquisition depends on distance to target and target size; NN/g summarizes its UI implication as larger targets being faster and less error-prone. ([OSHA][7])

V0 reuse role:

```text
viewing distance        -> visual-angle conversion and sensitivity analysis
Fitts-style reasoning   -> target/spacing inflation for frequent, far, high-risk, or coarse-pointer actions
ergonomic presets       -> default viewing-distance classes when actual value is unknown
```

Do not overfit v0 to medical acuity models. Treat user visual acuity, contrast sensitivity, and motor precision as optional declared profile fields with conservative fallbacks and visible ambiguity markers.

## 3.5 Constraint and layout solvers

The repo already uses Z3 in its validation/kernel ecosystem, so Z3 is a natural fit for hard feasibility checks and reason-coded unsat/blocking witnesses. Z3 is a Microsoft Research theorem prover with bindings for several languages. ([GitHub][8])

For bounded enumeration and optimization, OR-Tools CP-SAT can be used later: Google describes constraint programming as finding feasible solutions from a large set of possibilities by applying constraints, and CP-SAT is appropriate when variables can be modeled discretely. ([Google for Developers][9])

For continuous linear layout constraints, Kiwi.js / Kiwi can serve as a Cassowary-style constraint solver. For layout simulation, Yoga can compute Flexbox-like layout, but it should never become the authority source for Morphic UX law. ([GitHub][10])

Reuse role:

```text
Z3              -> hard rule feasibility, contradiction checks, blocked-variant witnesses
CP-SAT          -> finite candidate selection/ranking once candidate space grows
Kiwi/Cassowary  -> continuous panel ratio and min/max geometry solving
Yoga            -> layout simulation backend, not semantic adjudicator
```

## 3.6 Accessibility automation and post-implementation checks

Axe-core, Pa11y, Lighthouse, and Playwright should be used downstream to check realized surfaces, not upstream to replace adjudication. Axe-core is an automated accessibility testing engine for websites and HTML-based UIs; Lighthouse is an open-source automated quality tool with accessibility audits; Pa11y is a command-line accessibility checker; Playwright supports accessibility testing and ARIA snapshots. ([GitHub][11])

Reuse role:

```text
axe/Pa11y/Lighthouse  -> regression and compliance evidence
Playwright            -> case replay, bounding-box extraction, ARIA snapshots, computed-style capture
adjudicator           -> source of Morphic law and case-specific instantiated invariant expectations
```

# 4. v0 problem boundary

## v0 should support

A realistic v0 should handle **web-based ADEU workbench surfaces** with explicit structural IR. The supported surface classes should initially be narrow:

```text
bounded workbench
dual-pane review shell
chat + evidence side panel
chart/monitoring dashboard
compact inspector panel
artifact inspector family derivative
```

Supported inputs:

```text
1. Existing constitutional UX artifacts
   - ux_domain_packet@1
   - ux_morph_ir@1
   - ux_surface_projection@1
   - ux_interaction_contract@1

2. Ergonomic case envelope
   - user ergonomic profile
   - display/screen envelope
   - viewing envelope
   - window occupancy mode
   - input mode
   - task posture

3. Component visibility contract
   - what must be readable
   - what must remain continuously visible
   - what must remain quickly targetable
   - what may collapse/degrade
   - what may never be hidden before commit

4. Candidate morph/projection set
   - maximized split pane
   - half-screen split pane
   - stacked narrow
   - hub-and-spoke
   - compact inspector
   - other bounded candidates
```

Supported outputs:

```text
instantiated invariant packet
allowed morph projection set
blocked configurations with reasons
preferred projection hints
sensitivity report
ambiguity/confidence markers
measurement/test obligations
```

## v0 should explicitly not attempt

```text
- no medical diagnosis or clinical modeling of visual impairment
- no automatic inference of user acuity from camera/biometrics
- no generic “make it look better” design advice
- no consumer-facing wizard
- no final layout authorship
- no replacement of ux_morph_ir@1 constitutional law
- no unconstrained generation of new morph axes
- no raw screenshot “vibe check” as authority
- no arbitrary component ontology
- no native-platform generalization beyond declared web workbench assumptions
- no full dynamic runtime personalization engine
```

## Tractability assumptions

```text
- structural IR exists or is supplied by the reasoning model
- user ergonomic profile may be partial; missing values produce conservative defaults + ambiguity markers
- display/viewing values may be declared, measured, or inferred; confidence must be recorded
- v0 works in CSS px plus optional physical-size/visual-angle estimation
- component classes come from a finite registry
- candidate morphs are supplied or generated from a small approved profile table
- deontic constraints are hard; utility preferences never override them
```

# 5. Core conceptual/entity model

The subsystem should use a typed model like this. Names are illustrative but close to repo style.

```ts
type Confidence = "verified" | "declared" | "measured" | "inferred" | "unknown";
type WindowOccupancyMode = "maximized" | "half_screen" | "quarter_screen" | "floating_panel" | "constrained_panel";
type InputMode = "mouse" | "touch" | "pen" | "hybrid";
type TaskPosture =
  | "glanceable"
  | "monitoring"
  | "editing"
  | "high_precision_action"
  | "long_read"
  | "multi_panel_comparison";

type ConstraintForce = "constitutional_hard" | "ergonomic_hard" | "utility_preference" | "aesthetic_free";

interface ErgonomicUserProfile {
  profile_id: string;
  visual_acuity_class?: "unknown" | "typical" | "reduced" | "custom";
  acuity_scale?: number;                 // conservative multiplier, not diagnosis
  contrast_sensitivity_class?: "unknown" | "typical" | "reduced" | "custom";
  legibility_tolerance?: "standard" | "large_text_preferred" | "high_contrast_preferred";
  motor_precision_class?: "unknown" | "fine" | "reduced" | "coarse";
  preferred_zoom_percent?: number;
  confidence: Confidence;
}

interface DisplayViewingEnvelope {
  envelope_id: string;
  css_viewport_px: { width: number; height: number };
  available_surface_px: { width: number; height: number };
  device_pixel_ratio?: number;
  physical_ppi?: number;
  browser_zoom_percent?: number;
  os_scaling_percent?: number;
  window_occupancy_mode: WindowOccupancyMode;
  viewing_distance_cm?: number;
  viewing_distance_confidence: Confidence;
  ppi_confidence: Confidence;
}

interface InteractionEnvelope {
  input_mode: InputMode;
  pointer_precision: "fine" | "coarse" | "mixed" | "unknown";
  hover_available: boolean | "unknown";
  keyboard_primary?: boolean;
  high_risk_action_target_inflation: boolean;
}

interface TaskEnvelope {
  posture: TaskPosture;
  risk_level: "low" | "medium" | "high" | "critical";
  trust_sensitivity: string;
  utility_weights: {
    trust_calibration: number;
    error_prevention: number;
    operator_speed: number;
    monitoring_continuity?: number;
    reading_comfort?: number;
  };
}

interface ComponentVisibilityContract {
  component_id: string;
  component_class:
    | "primary_text"
    | "dense_data_table"
    | "chart"
    | "evidence_panel"
    | "status_surface"
    | "trust_boundary"
    | "commit_gate"
    | "advisory_action_cluster"
    | "destructive_action"
    | "navigation_lane";
  semantic_role: string;
  visibility_requirement:
    | "continuously_visible"
    | "same_context_reachable"
    | "progressive_reveal_allowed"
    | "collapsible"
    | "degradable"
    | "optional";
  readability_requirement:
    | "glance_readable"
    | "normal_readable"
    | "dense_reference"
    | "long_read"
    | "not_textual";
  targetability_requirement:
    | "quickly_targetable"
    | "normal_targetable"
    | "rare_target"
    | "not_interactive";
  collapse_policy:
    | "never_before_commit"
    | "may_collapse_with_inline_summary"
    | "may_collapse_to_icon"
    | "may_hide_when_nonessential";
  constitutional_invariant_refs: string[];
}

interface SurfaceInvariantPacket {
  reference_surface_family: string;
  reference_instance_id: string;
  approved_profile_id?: string;
  constitutional_invariants: string[];
  allowed_morph_axes: Record<string, string[]>;
  free_aesthetic_variables: string[];
  source_artifact_refs: string[];
  source_hashes?: Record<string, string>;
}

interface InstantiatedInvariant {
  invariant_id: string;
  force: ConstraintForce;
  scope_refs: string[];
  statement: string;
  value?: number | string | boolean | object;
  min?: number;
  max?: number;
  unit?: "css_px" | "mm" | "arcmin" | "ratio" | "columns" | "percent";
  source_basis: string[];
  confidence: Confidence;
}

interface BlockedConfiguration {
  configuration_id: string;
  reason_code: string;
  violated_force: ConstraintForce;
  violated_refs: string[];
  explanation: string;
  repair_hints: string[];
}

interface ErgonomicAdjudicationResult {
  result_id: string;
  judgment: "pass" | "needs_review" | "fail";
  instantiated_invariants: InstantiatedInvariant[];
  allowed_morph_projection_set: AllowedMorphProjection[];
  blocked_configurations: BlockedConfiguration[];
  preferred_projection?: PreferredProjection;
  ambiguity_markers: string[];
  confidence_summary: Record<string, Confidence>;
  measurement_obligations: string[];
}
```

The important point is not the exact TypeScript. The important point is that the model has **separate slots** for constitutional law, instantiated law, and aesthetic freedom.

## O/E/D/U placement in the entity model

```text
Ontology:
  UserProfile, DisplayViewingEnvelope, InteractionEnvelope, TaskEnvelope,
  ComponentVisibilityContract, CandidateProjection.

Epistemics:
  confidence fields, source_basis, measured/declared/inferred flags,
  ppi/viewing-distance uncertainty, visual witness refs.

Deontics:
  constitutional_invariants, required visibility, never-before-commit rules,
  blocked configurations, hard floors.

Utility:
  utility_weights, preferred_projection ranking, density/speed/readability tradeoffs.
```

# 6. Proposed artifact/schema family

V0 should not introduce a large platform. It should introduce a **small ergonomic adjudication family** that binds to existing UX artifacts.

## Minimal v0 artifact ladder

```text
ux_ergonomic_case_envelope@1
  Captures user + display + viewing + interaction + task envelope.

ux_component_visibility_contract@1
  Captures component-specific obligations and degradation permissions.

ux_ergonomic_adjudication_request@1
  Binds existing UX constitutional artifacts + case envelope + component contract
  + optional candidate morph set.

ux_ergonomic_adjudication_result@1
  Emits instantiated invariants, allowed/blocked morphs, preference ordering,
  ambiguity markers, and measurement obligations.
```

## Optional but valuable by v0.5

```text
ux_ergonomic_rulebook@1
  Versioned local policy constants derived from standards, platform presets,
  and ADEU-specific risk inflation.

ux_visual_witness_binding@1
  Binds visual/image witnesses or DOM measurements to structural IR, without
  allowing raw images to become authority.
```

## Schema envelope posture

Use the repo’s existing closed-root, schema-discriminated style:

```json
{
  "schema": "ux_ergonomic_adjudication_request@1",
  "reference_surface_family": "artifact_inspector_advisory_workbench",
  "reference_instance_id": "artifact_inspector_reference_main",
  "approved_profile_id": "artifact_inspector_reference",
  "source_artifacts": {
    "ux_domain_packet_ref": "...",
    "ux_morph_ir_ref": "...",
    "ux_surface_projection_ref": "...",
    "ux_interaction_contract_ref": "..."
  },
  "case_envelope_ref": "...",
  "component_visibility_contract_ref": "...",
  "candidate_projection_refs": [],
  "authority_boundary_policy": {
    "no_free_form_ui_codegen_without_ir": true,
    "no_visual_authority_inflation": true,
    "ui_artifacts_may_express_but_may_not_mint_authority": true,
    "ergonomic_adjudicator_may_not_rewrite_constitutional_invariants": true
  }
}
```

## Result payload shape

```json
{
  "schema": "ux_ergonomic_adjudication_result@1",
  "reference_surface_family": "artifact_inspector_advisory_workbench",
  "reference_instance_id": "artifact_inspector_reference_main",
  "request_ref": "apps/api/fixtures/ux_ergonomics/.../request.json",
  "overall_judgment": "needs_review",
  "constitutional_invariant_refs_preserved": [
    "evidence_before_commit_visibility",
    "trust_boundary_clarity",
    "destructive_action_gating"
  ],
  "instantiated_invariants": [
    {
      "invariant_id": "erg.text.body.min",
      "force": "ergonomic_hard",
      "scope_refs": ["primary-work-region", "evidence-lane"],
      "min": 16,
      "unit": "css_px",
      "confidence": "declared",
      "source_basis": ["wcag_resize_text", "case_envelope.viewing_distance"]
    },
    {
      "invariant_id": "erg.target.commit.min",
      "force": "ergonomic_hard",
      "scope_refs": ["commit-actions"],
      "min": 44,
      "unit": "css_px",
      "confidence": "verified",
      "source_basis": ["wcag_target_size_enhanced", "risk_inflation.commit_gate"]
    }
  ],
  "allowed_morph_projection_set": [
    {
      "projection_id": "compact_single_column_same_context",
      "allowed": true,
      "required_collapses": ["navigation-lane", "secondary-chart-list"],
      "required_pins": ["status-lane", "trust-boundary-lane", "commit-gate"],
      "score": 0.81
    }
  ],
  "blocked_configurations": [
    {
      "configuration_id": "quarter_screen_three_column",
      "reason_code": "ERG_BLOCK_PANEL_WIDTH_BELOW_READABLE_FLOOR",
      "violated_force": "ergonomic_hard",
      "violated_refs": ["evidence-lane", "chart-main"],
      "repair_hints": ["reduce_to_single_column", "collapse_secondary_panel_same_context"]
    }
  ],
  "free_aesthetic_variables_preserved": [
    "border_radius",
    "shadow_depth",
    "non_authority_color_theme"
  ],
  "ambiguity_markers": [
    "physical_ppi_inferred",
    "user_acuity_unknown"
  ]
}
```

# 7. Adjudicator input/output contract

## Input contract

The adjudicator accepts a **request**, not a prompt.

```text
Input = {
  surface_invariant_packet,
  ergonomic_case_envelope,
  component_visibility_contract,
  candidate_morph_projection_set?,
  rulebook_ref,
  visual_witness_binding?
}
```

Hard input requirements:

```text
- every adjudication must bind to a reference_surface_family
- every adjudication must bind to source UX artifacts or declare inference posture
- every component visibility contract must say what can collapse/degrade
- every candidate projection must expose regions, lanes, action clusters, and state surfaces
- missing user/screen/distance data must become ambiguity, not hidden default certainty
```

## Output contract

The output should be structured into five parts.

### 1. Case metrics

```text
available_surface_css_px
estimated_css_px_to_mm
estimated_visual_angle_by_font_role
input_precision_class
window_occupancy_mode
task_posture
confidence per measurement
```

### 2. Instantiated invariants

```text
minimum text size by role
minimum line height / line length by posture
minimum target size by action class and input mode
minimum spacing around targets
panel width ranges
column count range
chart plot-area floors
table row-height floors
pinned region obligations
collapse/degradation rules
same-context reachability obligations
```

### 3. Allowed and blocked morphs

```text
allowed_morph_projection_set:
  allowed profiles, required collapses, required pins, range constraints

blocked_configurations:
  candidate id, violated invariant, force level, reason code, repair hint
```

### 4. Preference ordering

```text
preferred_projection:
  top feasible projection
  utility score
  utility components
  deontic constraints satisfied
  remaining ambiguity
```

This is not final design authority. It is a ranked preference inside a lawful set.

### 5. Measurement obligations

```text
Playwright bounding box tests
computed style assertions
target size assertions
axe-core / WCAG checks
same-context evidence reachability checks
visual witness consistency checks
```

# 8. Architecture and solver boundary

## Architecture

```text
Reasoning model
  derives intended surface object
  identifies constitutional invariants
  supplies or derives candidate morphs
        |
        v
Ergonomic Instantiation Adjudicator
  normalizes case envelope
  computes ergonomic floors/ranges
  evaluates candidates
  blocks unlawful configurations
  ranks feasible candidates
  emits structured result
        |
        v
Reasoning model
  chooses concrete projection within allowed set
  records rationale / unresolved ambiguity
        |
        v
Coding agent
  implements selected projection
  exposes bindings and test anchors
        |
        v
Diagnostics / conformance
  verifies realized surface against UX + ergonomic artifacts
```

## Solver boundary

The adjudicator computes:

```text
1. Effective surface
   - available width/height after window mode and bounded workbench constraints
   - uncertainty if dimensions are inferred

2. Readability floors
   - text-size floors by component role
   - line-height/line-length constraints
   - dense-data limits
   - visual-angle estimates when distance/PPI confidence permits

3. Targetability floors
   - minimum target size by input mode
   - risk inflation for commit/destructive/high-frequency controls
   - spacing and collision constraints

4. Structural feasibility
   - max simultaneous columns
   - min/max panel widths
   - required pinned surfaces
   - allowed collapses and degradation routes
   - chart/table minimum readable dimensions

5. Candidate ranking
   - pass/fail/needs_review
   - utility score only after hard constraints
   - sensitivity to window shrinkage, distance, acuity scale, and input mode

6. Exclusion evidence
   - blocked configurations with reason codes
   - violated source refs
   - minimal repair hints
```

The adjudicator does **not** compute:

```text
- the constitutional invariants themselves
- new UX semantics
- final visual design
- color palettes, shadows, border-radius, decorative motion
- trust authority
- content truth
- clinical visual diagnosis
- raw image-only judgments
```

## Constraint force ordering

The solver should use a fixed ordering:

```text
constitutional_hard
  > ergonomic_hard
  > utility_preference
  > aesthetic_free
```

A utility objective such as operator speed may choose between two feasible layouts. It may not override evidence-before-commit, destructive action gating, text legibility floors, or target-size floors.

## Example reason codes

```text
ERG_BLOCK_TEXT_BELOW_CASE_FLOOR
ERG_BLOCK_TARGET_BELOW_INPUT_FLOOR
ERG_BLOCK_PANEL_WIDTH_BELOW_READABLE_FLOOR
ERG_BLOCK_CHART_BELOW_MIN_PLOT_AREA
ERG_BLOCK_EVIDENCE_NOT_SAME_CONTEXT_REACHABLE
ERG_BLOCK_COMMIT_GATE_NOT_CONTINUOUSLY_VISIBLE
ERG_BLOCK_WINDOW_MODE_COLLAPSE_UNDECLARED
ERG_WARN_USER_ACUITY_UNKNOWN_DEFAULT_APPLIED
ERG_WARN_PPI_INFERRED_NOT_MEASURED
ERG_WARN_VISUAL_WITNESS_STRUCTURAL_MISMATCH
```

# 9. Interaction with visual/image-based surface workflows

The visual/image workflow should be treated as a **witness workflow**, not as the governing substrate.

Correct relation:

```text
structural IR
  = authority-bearing surface description

visual projection / image
  = witness, reference carrier, rendered consequence, measurement object

visual witness binding
  = explicit mapping from rendered geometry back to structural roles
```

The adjudicator should not accept:

```text
"screenshot.png" -> "looks too dense"
```

as an authoritative adjudication input.

It should accept:

```json
{
  "schema": "ux_visual_witness_binding@1",
  "surface_ref": "artifact_inspector_reference_main",
  "witness_kind": "rendered_dom_capture",
  "viewport_px": { "width": 720, "height": 900 },
  "element_measurements": [
    {
      "source_ref": "lane:evidence-lane",
      "bounding_box_px": { "x": 16, "y": 88, "width": 688, "height": 240 },
      "computed_font_size_px": 15,
      "computed_line_height_px": 22,
      "visibility": "same_context_visible"
    }
  ]
}
```

For invariant-bearing images generated upstream, the image can carry a projected reference, but the adjudicator still needs a structural interpretation:

```text
image witness
  -> structural interpretation / bounding boxes / semantic role map
  -> adjudication
```

If structural IR and image witness disagree, v0 should not guess. It should emit:

```text
ERG_WARN_VISUAL_WITNESS_STRUCTURAL_MISMATCH
or
ERG_BLOCK_AUTHORITY_REQUIRES_STRUCTURAL_IR
```

This preserves ADEU’s source-of-truth discipline: images can strengthen evidence, reveal implementation drift, and guide reasoning, but they cannot silently replace typed law.

# 10. Role of reasoning model vs tool vs coding agent

## Reasoning model

The reasoning model remains the higher-order judge. It owns:

```text
- recovering or deriving the intended surface object
- separating constitutional invariants from morphable choices
- selecting candidate morph profiles to test
- deciding which utility tradeoffs matter for this user/task
- interpreting ambiguity markers
- choosing the concrete projection from allowed ranges
- recording why a lawful projection was chosen
```

The reasoning model must not use the adjudicator as a taste engine. It asks bounded questions such as:

```text
Given this surface invariant packet and this case envelope,
is a three-column projection still lawful?

What minimum target floor applies to commit actions under touch + high risk?

At what width must the evidence panel collapse, and what same-context reveal is still allowed?

Which candidate projections are blocked, and by which force level?
```

## Ergonomic Instantiation Adjudicator

The tool owns bounded computation:

```text
- floors
- ranges
- feasibility
- exclusions
- ranking of supplied candidates
- sensitivity analysis
- reason-coded output
```

It does not own semantic meaning, final design choice, or implementation.

## Coding agent

The coding agent receives:

```text
ux_surface_projection@1
+ ux_interaction_contract@1
+ ux_ergonomic_adjudication_result@1
+ selected projection decision record
+ implementation observable binding requirements
```

The coding agent implements within the selected constraints. It may not decide that a blocked configuration is acceptable because it “looks cleaner.”

## Handoff logic

```text
1. Reasoning model composes request.
2. Adjudicator emits result.
3. Reasoning model selects projection:
     - must be in allowed_morph_projection_set
     - must cite unresolved ambiguity
     - must not bind free aesthetics prematurely
4. Coding agent implements:
     - uses structural roles first
     - emits stable data attributes / hooks
     - keeps measurable target/text/panel constraints
5. Diagnostics compare realized surface:
     - existing UX conformance
     - ergonomic measurement obligations
     - visual witness consistency if present
```

# 11. v0 implementation slices

## Slice 0 — support note and naming decision

Create a support doc, not a lock yet:

```text
docs/support/DRAFT_UX_ERGONOMIC_INSTANTIATION_ADJUDICATOR_v0.md
```

Purpose:

```text
- freeze the distinction between constitutional invariants, instantiated invariants, and aesthetics
- name v0 scope
- list deferred seams
- propose schema family
```

## Slice 1 — schemas and fixtures only

Add schemas in the same spirit as existing UX governance schemas:

```text
packages/adeu_core_ir/schema/ux_ergonomic_case_envelope.v1.json
packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_adjudication_request.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_adjudication_result.v1.json
```

Add accepted and rejected fixtures:

```text
apps/api/fixtures/ux_ergonomics/vnext_plusXX/
  ergonomic_case_envelope_desktop_reference.json
  component_visibility_contract_review_shell_reference.json
  ergonomic_adjudication_request_reference.json
  ergonomic_adjudication_result_reference.json
  ergonomic_adjudication_result_reject_missing_visibility_contract.json
  ergonomic_adjudication_result_reject_constitutional_rewrite.json
  ergonomic_adjudication_result_reject_raw_image_only.json
```

## Slice 2 — deterministic validator and canonicalizer

Add a thin Pydantic/canonicalization module:

```text
packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py
```

Initial validators:

```text
- closed-root schemas
- required schema discriminator
- source artifact refs present
- constitutional refs are read-only
- free aesthetic variables cannot satisfy hard constraints
- component visibility contract exists for every required region/lane/action cluster
- blocked configurations carry reason codes and violated refs
```

This slice should not need Z3 or OR-Tools.

## Slice 3 — rulebook and scalar calculator

Add `ux_ergonomic_rulebook@1` as a versioned artifact or embedded constants:

```text
- WCAG target floors
- platform target presets
- contrast floors
- text spacing / line length guards
- input-mode target inflation
- risk/action inflation
- default ambiguity behavior
```

Implement deterministic calculations:

```text
- available surface classification
- target floor by input mode/action risk
- text floor by role/user profile
- panel width feasibility
- column-count feasibility
- chart/table minimum-size checks
```

This is where the “ergonomic visual calculator” intuition lives, but only as one internal component of the adjudicator.

## Slice 4 — candidate projection evaluator

Input:

```text
candidate projections supplied by reasoning model or approved profile table
```

Output:

```text
allowed_morph_projection_set
blocked_configurations
preferred_projection
sensitivity_report
```

Keep candidate space tiny at first:

```text
- maximized_split
- half_screen_split
- narrow_stacked
- compact_single_column
```

## Slice 5 — Playwright measurement bridge

Add a measurement harness that can run a route under specified viewport/window modes and emit:

```text
- bounding boxes
- computed font sizes
- target hit-area boxes
- visibility of pinned/same-context regions
- ARIA snapshot if relevant
```

Then compare measured implementation against `ux_ergonomic_adjudication_result@1`.

## Slice 6 — integrate with existing UX diagnostics/conformance

Add new diagnostics families:

```text
ergonomic_target_floor_violation
ergonomic_text_floor_violation
ergonomic_panel_width_violation
ergonomic_pinned_surface_missing
ergonomic_collapse_unlawful
ergonomic_visual_witness_mismatch
ergonomic_case_envelope_ambiguity_unresolved
```

Do not mix them with taste diagnostics. Keep them reason-coded.

## Slice 7 — optional solver backend

Only after deterministic rules hit real complexity:

```text
- Z3 for hard feasibility / unsat cores
- Kiwi for panel ratio solving
- OR-Tools CP-SAT for finite variant optimization
```

V0 can start without a heavy solver. The initial object can be a rule-based adjudicator with a clear seam for solver substitution.

# 12. Failure modes and guardrails

## False precision

Risk: the tool emits `font-size: 15.3px` as though it were scientifically exact.

Guardrail:

```text
- output ranges, not fake absolutes
- record measured/declared/inferred confidence
- expose ambiguity markers
- require rulebook version refs
- use visual-angle estimates as evidence, not clinical truth
```

## Overbinding aesthetics

Risk: border radius, shadows, color flavor, decorative density, or animation tone become “invariants.”

Guardrail:

```text
- schema separates free_aesthetic_variables
- validators reject aesthetic variables as hard constraints
- color hue remains free unless it carries contrast, authority, warning, status, or evidence semantics
```

## Underbinding layout law

Risk: the tool says “responsive stack is fine” while evidence-before-commit or trust-boundary visibility disappears.

Guardrail:

```text
- component_visibility_contract required
- same-context reachability checked structurally
- commit/destructive gates must bind to evidence requirements
- hidden lanes require declared lawful collapse route
```

## Ignoring user-specific acuity or viewing distance

Risk: the surface passes because it meets generic desktop assumptions.

Guardrail:

```text
- user profile and viewing envelope are first-class
- missing acuity/distance creates ambiguity markers
- conservative defaults apply only with explicit confidence downgrade
- sensitivity report shows what changes under distance/acuity inflation
```

## Treating quarter-screen as maximized

Risk: the surface keeps the same 3-column law under a quarter-screen window.

Guardrail:

```text
- window_occupancy_mode is required
- available_surface_px is primary, not nominal device class
- each projection evaluated under actual available surface
- blocked if columns/panels fall below floors
```

## Invisible semantic drift

Risk: the instantiated projection remains ergonomic but no longer represents the same surface object.

Guardrail:

```text
- result binds to ux_morph_ir@1 and ux_surface_projection@1 refs/hashes
- constitutional refs are read-only
- every allowed morph must preserve declared invariants
- result cannot introduce new semantic grouping or authority posture
```

## Image vibe substitution

Risk: an invariant-bearing screenshot is treated as enough.

Guardrail:

```text
- structural IR remains primary
- visual witness requires semantic role mapping
- image-only requests fail or become advisory
- screenshot/DOM mismatch is reason-coded
```

## Solver infeasibility hidden by fallback

Risk: the tool silently picks a degraded layout when constraints conflict.

Guardrail:

```text
- infeasible means blocked or needs_review
- emit minimal violated constraint set where possible
- repair hints are suggestions, not implicit authorization
```

# 13. Worked examples

## Example 1 — chart-heavy trading / monitoring surface

### Case A: maximized desktop monitoring

```text
Surface:
  chart-heavy trading surface

Task posture:
  monitoring + high-precision action

Input:
  mouse, keyboard, occasional high-risk commit

Envelope:
  maximized desktop, large available surface, declared 70 cm viewing distance

Constitutional invariants:
  risk/status continuously visible
  order/commit gate separated from advisory analytics
  evidence/rationale for signal visible before commit
  destructive or irreversible order action gated
```

Likely adjudicator result:

```text
Allowed:
  - multi-panel layout
  - 2–3 columns if chart plot-area floors pass
  - dense watchlist if row height/text floor pass
  - pinned risk/status strip
  - separated commit action cluster

Blocked:
  - placing order controls inside chart hover overlay
  - hiding risk/status behind tab/drawer
  - chart thumbnails whose axis labels fall below text floor
  - same visual styling for advisory signal and executable order
```

Morphic reading:

```text
The trading surface can remain the same semantic object while instantiating
a high-density monitoring projection, because the case envelope justifies
simultaneous panels and the visibility contract preserves risk/status/commit law.
```

### Case B: quarter-screen floating panel

```text
Envelope:
  quarter-screen floating panel

Task posture:
  glanceable monitoring, not active trading

Input:
  mouse or hybrid
```

Likely adjudicator result:

```text
Allowed:
  - single primary chart or sparkline summary
  - pinned risk/status
  - collapsed watchlist with same-context reveal
  - commit action hidden or disabled unless full evidence context is restored

Blocked:
  - 3-column chart grid
  - dense order ladder below target floor
  - executable commit button without same-context risk/evidence visibility
```

The key difference is not “breakpoint changed.” The **task posture and window occupancy changed the instantiated invariants**. The semantic object may remain a trading monitor, but active high-risk execution is no longer justified in the compact projection unless the evidence/gate requirements are restored.

## Example 2 — dual-pane review shell

```text
Surface:
  dual-pane review shell for artifact/source comparison

Constitutional invariants:
  source/evidence before approval
  advisory vs authoritative distinction
  status truth visible
  commit/handoff gate explicit
  semantic grouping between artifact, evidence, diagnostics, and action clusters preserved
```

### Expert desktop, mouse, maximized

Likely output:

```text
Instantiated invariants:
  source pane min width: range sufficient for readable line length
  evidence pane: continuously visible or same-context visible
  diagnostics lane: pinned or adjacent to evidence
  commit gate: visually later than evidence review
  target floor: WCAG AA minimum for ordinary actions, inflated for commit

Allowed:
  split-pane review
  high density
  keyboard fast path
  compact advisory controls

Blocked:
  approval button in same toolbar as advisory filter
  source pane too narrow for stable text scanning
  diagnostics only reachable through route transition
```

### Same shell, reduced acuity / long-read posture

Likely output:

```text
Instantiated invariants:
  larger text floor
  reduced density ceiling
  fewer simultaneous columns
  increased line height
  evidence pane remains same-context reachable but may become stacked

Allowed:
  stacked source-over-evidence layout
  hub-and-spoke only if evidence reveal is same-context and before commit

Blocked:
  dense side-by-side panes with truncated text
  small icon-only diagnostics
  collapses that make source/evidence comparison require route replacement
```

The constitutional object does not change. The instantiated invariants do.

## Example 3 — compact quarter-screen inspector

```text
Surface:
  compact inspector for artifact metadata / status / quick action

Envelope:
  640×720-ish floating panel
  quarter-screen
  mixed input
  glanceable + quick inspection

Constitutional invariants:
  authoritative/provisional status distinction
  trust boundary visible
  destructive action gated
  evidence link same-context reachable
```

Likely adjudicator result:

```text
Allowed:
  one-column inspector
  status/trust strip pinned at top
  primary metadata readable
  evidence collapsed behind same-context reveal
  advisory action cluster visible
  destructive action moved behind explicit gate or omitted

Blocked:
  dual-pane diff
  miniature evidence table with unreadable rows
  icon-only trust boundary
  destructive action in overflow menu without gate explanation
```

This is a strong v0 target because it tests the exact problem: the compact surface must not pretend to be the maximized surface, but it must also remain the same lawful object.

## Example 4 — chat + evidence side panel

```text
Surface:
  chat workbench with evidence side panel

Constitutional invariants:
  answer/proposal is not authoritative unless grounded
  evidence before commit or external handoff
  provenance and confidence visible
  user can inspect evidence without leaving bounded workbench
```

### Wide desktop

Likely result:

```text
Allowed:
  chat lane + evidence lane side by side
  status/provenance pinned
  evidence snippets continuously visible
  high operator speed

Blocked:
  final action button before evidence lane has loaded
  evidence hidden behind route transition
```

### Narrow/quarter-screen

Likely result:

```text
Allowed:
  chat primary
  evidence panel collapsed into same-context reveal
  evidence summary pinned near proposal
  commit button disabled until evidence reveal has been visited or remains visible

Blocked:
  evidence available only on another page
  commit action at bottom of chat with no adjacent provenance/status
  tiny citation chips below target/legibility floor
```

Again, responsive stacking is not enough. The adjudicator determines whether the **evidence-before-commit invariant** can be lawfully instantiated under narrow geometry.

# 14. Final recommendation

Build this as **`ux_ergonomic_adjudication`**, with the human-readable subsystem name **Ergonomic Instantiation Adjudicator**.

Do not start with a broad solver. Start with:

```text
1. schema family
2. rulebook constants
3. deterministic case-envelope calculator
4. component visibility contract
5. candidate projection evaluator
6. reason-coded blocked configurations
7. Playwright/axe measurement bridge
```

Place the first schemas and validators near the existing UX governance family, because v0 is an extension of `ux_morph_ir@1` / `ux_surface_projection@1`, not a separate design-system platform. Keep the solver seam open for Z3, Kiwi, or CP-SAT later, but do not make solver cleverness the first milestone.

The governing principle should be:

```text
The adjudicator may bind concrete ergonomic instantiation.
It may not rewrite the semantic object.
It may not promote aesthetic preference into law.
It may not substitute screenshots for structural authority.
It may not let utility outrank deontic invariants.
```

That gives Morphic UX the missing middle layer: a lawful descent mechanism from stable surface object to concrete, case-specific UI projection.

[1]: https://developer.mozilla.org/en-US/docs/Web/CSS/Guides/Media_queries/Using "Using media queries - CSS | MDN"
[2]: https://www.w3.org/TR/WCAG22/ "Web Content Accessibility Guidelines (WCAG) 2.2"
[3]: https://www.w3.org/WAI/WCAG22/Understanding/target-size-minimum.html "Understanding Success Criterion 2.5.8: Target Size (Minimum) | WAI | W3C"
[4]: https://www.w3.org/WAI/WCAG22/Understanding/text-spacing.html?utm_source=chatgpt.com "Understanding Success Criterion 1.4.12: Text Spacing | WAI"
[5]: https://developer.apple.com/design/tips/ "UI Design Dos and Don’ts - Apple Developer"
[6]: https://developer.mozilla.org/en-US/docs/Web/API/Window/devicePixelRatio?utm_source=chatgpt.com "Window: devicePixelRatio property - Web APIs | MDN"
[7]: https://www.osha.gov/etools/computer-workstations/components/monitors "eTools : Computer Workstations - Workstation Components - Monitors | Occupational Safety and Health Administration"
[8]: https://github.com/z3prover/z3 "GitHub - Z3Prover/z3: The Z3 Theorem Prover · GitHub"
[9]: https://developers.google.com/optimization/cp "Constraint Optimization  |  OR-Tools  |  Google for Developers"
[10]: https://github.com/IjzerenHein/kiwi.js/?utm_source=chatgpt.com "IjzerenHein/kiwi.js: Fast TypeScript implementation of the ..."
[11]: https://github.com/dequelabs/axe-core "GitHub - dequelabs/axe-core: Accessibility engine for automated Web UI testing · GitHub"
