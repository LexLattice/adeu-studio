# 1. Executive delta judgment

The retained baseline is sound. The hardening required before implementation is to make the adjudicator **artifact-bound, rule-provenanced, finite-registry-driven, and epistemically strict**.

The v0.1 slice should not start by “solving layout.” It should start by preventing five implementation hazards:

```text
1. hidden ergonomic rules
2. free-form candidate projections
3. drifting component taxonomy
4. inadmissible physical/visual calculations
5. fake precision in pass/fail/scoring
```

The concrete recommendation is to add a new repo-native module:

```text
packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py
```

with schemas exported beside the existing UX governance schemas:

```text
packages/adeu_core_ir/schema/ux_ergonomic_rule_authority_stack.v1.json
packages/adeu_core_ir/schema/ux_component_ergonomic_registry.v1.json
packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json
packages/adeu_core_ir/schema/ux_candidate_projection_profile_table.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_case_envelope.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_adjudication_request.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_adjudication_result.v1.json
```

This should be treated as an extension of the current `ux_governance` lane, not a replacement for it. The existing repo already has the right pattern: closed Pydantic models, schema discriminators, `extra="forbid"`, frozen enumerations, canonicalization helpers, schema export to `spec/`, and fixtures under `apps/api/fixtures/ux_governance/vnext_plus61` through `vnext_plus65`.

The new lane should follow that style exactly.

# 2. What the prior note got right and is now retained

Retained without restart:

```text
Subsystem name:
  Ergonomic Instantiation Adjudicator

Subsystem role:
  bounded adjudicator, not designer, not final judge, not consumer wizard

Core separation:
  constitutional invariants
  instantiated invariants
  free aesthetic variables

Pipeline:
  reasoning model derives surface object
  adjudicator computes lawful case-specific constraints
  reasoning model chooses projection
  coding agent implements
  diagnostics/conformance verify

Image posture:
  image/rendered surface is witness only
  structural IR remains primary authority

v0 posture:
  narrow, web/workbench-first, rule-bound, finite candidates, explicit ambiguity
```

The hardening pass below only resolves the underbound implementation seams.

# 3. Authority stack hardening

## 3.1 Required authority order

The adjudicator must evaluate rules in a fixed authority stack. No platform preset, user preference, or utility heuristic may silently override constitutional or ADEU deontic law.

| Rank | Layer                                          | Artifact source                                                                  | Force                                                        | Override behavior                                                                                   |
| ---: | ---------------------------------------------- | -------------------------------------------------------------------------------- | ------------------------------------------------------------ | --------------------------------------------------------------------------------------------------- |
|    0 | **Constitutional surface invariants**          | Existing `ux_morph_ir@1`, `ux_surface_projection@1`, `ux_interaction_contract@1` | Hard blocking                                                | Cannot be overridden by ergonomic rule, platform preset, user preference, or utility.               |
|    1 | **Repo-local ADEU deontic / ergonomic policy** | New `ux_ergonomic_rule_authority_stack@1` plus existing UX deontics              | Hard blocking or hard floor                                  | May raise external/platform floors; may not weaken constitutional law.                              |
|    2 | **External standards floors**                  | Versioned rule entries, for example WCAG-derived floors                          | Hard floor when adopted by rulebook                          | May be strengthened by ADEU policy or user preference; may not be lowered by platform/user/utility. |
|    3 | **Platform presets**                           | Apple / Android / Windows style presets                                          | Default preset unless explicitly adopted as ADEU hard policy | May raise default floors for an input mode; may not lower external or ADEU floors.                  |
|    4 | **User-specific declared preferences**         | `ux_ergonomic_case_envelope@1`                                                   | Preference or user floor inflation                           | May raise text/target/spacing floors; may not lower hard floors or hide required components.        |
|    5 | **Heuristic utility weights**                  | Request/result utility section                                                   | Advisory ranking only                                        | Never blocks alone and never overrides hard law.                                                    |

External standard examples should be imported as explicit rule entries, not hidden constants. WCAG target-size minimum uses a 24×24 CSS px floor with exceptions, WCAG target-size enhanced uses 44×44 CSS px, and WCAG contrast guidance treats 3:1 and 4.5:1 as threshold values rather than rounded suggestions. These belong in the rulebook as external standard floors, not as broad “accessibility compliance magic.” ([W3C][1])

Platform presets should be stored separately from standards floors. For example, Apple’s button guidance gives a 44×44 pt hit-region rule of thumb, Android accessibility guidance recommends at least 48×48 dp touch targets, and Microsoft Windows guidance gives a 7.5 mm / 40×40 px touch target rule of thumb for Windows apps. Those are useful presets, but in this adjudicator they do not become authority unless the ADEU rulebook explicitly adopts them. ([Apple Developer][2])

## 3.2 New rule artifact

Add:

```text
schema: ux_ergonomic_rule_authority_stack@1
file: packages/adeu_core_ir/schema/ux_ergonomic_rule_authority_stack.v1.json
model: UXErgonomicRuleAuthorityStack
```

Each rule entry should be provenance-bearing:

```json
{
  "rule_id": "erg.target.pointer.wcag_2_2_aa_min_24_css_px",
  "authority_layer": "external_standard_floor",
  "force": "hard_floor",
  "source_kind": "external_standard",
  "source_ref": "WCAG_2_2_SC_2_5_8",
  "adopted_by_repo_policy": true,
  "applies_to": {
    "input_modes": ["mouse", "pen", "hybrid", "touch"],
    "component_classes": ["erg_advisory_action_cluster", "erg_comparison_action_cluster"]
  },
  "constraint": {
    "metric": "target_min_size",
    "min": 24,
    "unit": "css_px"
  },
  "override_policy": {
    "may_raise": true,
    "may_lower": false,
    "may_override_constitutional_invariant": false,
    "may_override_repo_deontic_policy": false,
    "may_override_external_standard_floor": false
  },
  "provenance": {
    "rulebook_version": "v0_1",
    "basis": ["external_standard_floor"],
    "confidence": "verified_reference"
  }
}
```

## 3.3 Rule composition semantics

For numeric minima:

```text
effective_floor = max(
  constitutional-derived floor if any,
  ADEU hard floor,
  adopted external standard floor,
  adopted platform hard floor,
  user-declared upward preference
)
```

For prohibitions:

```text
any constitutional/deontic prohibition wins absolutely
```

For utility:

```text
utility can rank only candidates that have already passed hard checks
```

For user preference:

```text
user preference may inflate:
  font size
  target size
  spacing
  contrast preference
  density comfort

user preference may not reduce:
  evidence visibility
  trust-boundary visibility
  commit gating
  destructive action gating
  target size below hard floor
  text size below hard floor
```

Required validator behavior:

```text
- reject any rule with may_lower=true against a higher-authority floor
- reject any platform preset marked hard unless adopted_by_repo_policy=true
- reject any user preference that attempts to lower a hard minimum
- reject any utility rule with force other than advisory_ranking
- reject any rule source without explicit provenance
```

# 4. Candidate projection artifact family

## 4.1 New candidate artifact

Add:

```text
schema: ux_candidate_projection_profile_table@1
file: packages/adeu_core_ir/schema/ux_candidate_projection_profile_table.v1.json
model: UXCandidateProjectionProfileTable
```

This is not the same as the existing `v36a_first_family_approved_profile_table@1`.

The existing profile table says:

```text
Which morph-axis tuples are approved for the surface family?
```

The new candidate projection table says:

```text
Which finite geometric/visibility projection shapes may the ergonomic adjudicator evaluate?
```

## 4.2 Relation to existing `ux_morph_ir@1`

A candidate projection profile must be a **case-evaluation overlay** over existing constitutional artifacts.

It may reference:

```text
ux_domain_packet@1
ux_morph_ir@1
ux_surface_projection@1
ux_interaction_contract@1
v36a_first_family_approved_profile_table@1
ux_surface_compiler_variant_manifest@1
```

It may not introduce:

```text
new regions
new lanes
new action clusters
new state-surface semantics
new authority posture
new evidence-before-commit law
new trust-boundary law
new morph axes not present in ux_morph_ir@1
```

Current repo binding should use the existing UX governance fixtures:

```text
apps/api/fixtures/ux_governance/vnext_plus61/ux_domain_packet_artifact_inspector_reference.json
apps/api/fixtures/ux_governance/vnext_plus61/ux_morph_ir_artifact_inspector_reference.json
apps/api/fixtures/ux_governance/vnext_plus61/v36a_first_family_approved_profile_table.json
apps/api/fixtures/ux_governance/vnext_plus62/ux_surface_projection_artifact_inspector_reference.json
apps/api/fixtures/ux_governance/vnext_plus62/ux_interaction_contract_artifact_inspector_reference.json
apps/api/fixtures/ux_governance/vnext_plus65/ux_surface_compiler_variant_manifest_artifact_inspector.json
```

## 4.3 Required candidate profile fields

A v0 candidate profile must carry enough structure to be evaluated without model interpretation.

Required fields:

```json
{
  "candidate_profile_id": "artifact_inspector_quarter_screen_inspector_safe_buffered",
  "reference_surface_family": "artifact_inspector_advisory_workbench",
  "reference_instance_id": "artifact_inspector_reference_main",
  "approved_profile_id": "artifact_inspector_alternate",

  "source_artifact_refs": {
    "ux_morph_ir_ref": "...",
    "ux_surface_projection_ref": "...",
    "ux_interaction_contract_ref": "...",
    "approved_profile_table_ref": "..."
  },

  "target_envelope": {
    "window_occupancy_modes": ["quarter_screen", "floating_panel"],
    "input_modes": ["mouse", "hybrid"],
    "task_postures": ["glanceable", "editing"],
    "viewport_width_range_css_px": { "min": 360, "max": 760 },
    "viewport_height_range_css_px": { "min": 480, "max": 1200 }
  },

  "projection_shape": {
    "shape_kind": "single_column_compact_inspector",
    "simultaneous_column_count": 1,
    "region_order": [
      "status-region",
      "primary-work-region",
      "evidence-region",
      "action-region",
      "navigation-region"
    ],
    "pinned_lane_ids": [
      "status-lane",
      "trust-boundary-lane"
    ],
    "collapsed_lane_policies": [
      {
        "lane_id": "evidence-lane",
        "collapse_mode": "same_context_reveal",
        "reveal_transition": "bounded_workbench_state_reveal",
        "summary_required": true
      }
    ]
  },

  "component_visibility_claims": [
    {
      "component_ref": "lane:evidence-lane",
      "visibility_state": "same_context_reachable",
      "collapse_policy": "may_collapse_with_inline_summary"
    }
  ],

  "action_targeting_claims": [
    {
      "component_ref": "action_cluster:commit-actions",
      "targeting_posture": "high_risk_gate",
      "continuous_visibility_required": true
    }
  ],

  "free_aesthetic_variables_declared": [
    "border_radius",
    "shadow_depth",
    "non_authority_color_theme"
  ]
}
```

## 4.4 Lawful vs underspecified candidate

A **lawful candidate** must satisfy all of these before ergonomic scoring:

```text
- binds to the same reference_surface_family and reference_instance_id as source UX artifacts
- uses an approved_profile_id present in v36a_first_family_approved_profile_table@1
- uses only region/lane/action/state refs already present in ux_surface_projection@1
- maps every required region/lane/action cluster to an ergonomic component class
- declares visibility state for every constitutional evidence/trust/status/commit-bearing component
- declares every collapse and reveal transition
- uses only same-context reveal terms from the same-context glossary
- does not replace a required evidence lane with route transition before commit
- does not create new semantic authority
- does not bind aesthetic variables as hard law
```

An **underspecified candidate** is not “bad design.” It is simply non-evaluable.

Underspecified examples:

```text
- "compact layout" with no region/lane visibility claims
- candidate lacks viewport range
- candidate references a lane not present in ux_surface_projection@1
- candidate says evidence is "hidden" but gives no same-context reveal
- candidate omits commit gate targetability posture
- candidate gives visual screenshot only without structural mapping
```

## 4.5 v0 candidate profiles should be fixed shapes

For v0.1, candidate profiles should be repo-native fixed shapes, not free-form reasoning-model proposals.

Initial candidate set:

```text
artifact_inspector_maximized_split_reference
  approved_profile_id: artifact_inspector_reference
  shape: multi-region split pane
  intended for: maximized desktop

artifact_inspector_half_screen_split_reference
  approved_profile_id: artifact_inspector_reference
  shape: reduced split pane
  intended for: half-screen desktop

artifact_inspector_narrow_stacked_same_context
  approved_profile_id: artifact_inspector_alternate
  shape: single-column stacked with same-context evidence reveal
  intended for: constrained narrow workbench

artifact_inspector_quarter_screen_inspector_safe_buffered
  approved_profile_id: artifact_inspector_alternate
  shape: compact inspector, status/trust pinned, commit gated
  intended for: quarter-screen or floating panel
```

The reasoning model may choose among these. It may not mint arbitrary new candidate shapes inside an adjudication request.

# 5. Component ergonomic registry

## 5.1 New registry artifact

Add:

```text
schema: ux_component_ergonomic_registry@1
file: packages/adeu_core_ir/schema/ux_component_ergonomic_registry.v1.json
model: UXComponentErgonomicRegistry
```

Also keep the per-surface contract separate:

```text
schema: ux_component_visibility_contract@1
file: packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json
model: UXComponentVisibilityContract
```

The registry defines the finite class vocabulary. The visibility contract maps a specific surface’s existing semantic parts into those classes.

## 5.2 Semantic role vs ergonomic role

Semantic role answers:

```text
What does this component mean in the Morphic UX object?
```

Ergonomic role answers:

```text
What human/device/task constraint does this component impose?
```

Example:

```text
semantic role:
  trust_boundary_lane

ergonomic class:
  erg_trust_boundary_surface

semantic invariant:
  trust boundary must remain distinguishable

ergonomic instantiated invariant:
  trust boundary must be continuously visible or pinned in compact mode;
  text/icon target must meet status legibility floor;
  contrast status must satisfy rulebook threshold.
```

## 5.3 Mandatory v0.1 classes

For the current repo’s artifact-inspector family, the mandatory ergonomic classes should be:

| Ergonomic class                  | Maps from existing UX source                                    | v0 role                                                 |
| -------------------------------- | --------------------------------------------------------------- | ------------------------------------------------------- |
| `erg_work_context_lane`          | `lane_role=work_context_lane`, `primary_work_region`            | Main task/read/edit surface.                            |
| `erg_source_text_lane`           | `lane_role=source_lane`                                         | Text/source artifact reading or comparison.             |
| `erg_evidence_lane`              | `lane_role=evidence_lane`                                       | Evidence-before-commit carrier.                         |
| `erg_diagnostics_lane`           | `lane_role=diagnostics_lane`                                    | Diagnostic/status explanation carrier.                  |
| `erg_status_surface`             | `status_lane`, authoritative/provisional/warning state surfaces | State truth legibility and continuous visibility.       |
| `erg_trust_boundary_surface`     | `trust_boundary_lane`                                           | Authority/provisional distinction visibility.           |
| `erg_navigation_lane`            | `navigation_lane`                                               | Workbench navigation and orientation.                   |
| `erg_advisory_action_cluster`    | `advisory_action_cluster`                                       | Reversible advisory actions.                            |
| `erg_comparison_action_cluster`  | `comparison_action_cluster`                                     | Source/evidence focus actions.                          |
| `erg_commit_gate_action_cluster` | `commit_action_cluster`, `commit_or_approval_gate`              | High-risk gate targetability and evidence precondition. |

Deferred classes:

```text
erg_dense_data_table
erg_chart_plot_area
erg_chart_axis_label_cluster
erg_chart_legend_cluster
erg_order_ladder
erg_time_series_monitoring_strip
erg_freeform_canvas
erg_map_surface
erg_media_timeline
```

These should be reserved but not admitted into v0.1 validation unless implemented.

## 5.4 Registry entry shape

Each class entry should include:

```json
{
  "class_id": "erg_commit_gate_action_cluster",
  "applies_to_surface_units": ["action_cluster"],
  "allowed_source_semantic_kinds": ["commit_action_cluster"],
  "default_visibility_requirement": "continuously_visible_when_commit_available",
  "default_targetability_requirement": "high_risk_quickly_targetable",
  "default_readability_requirement": "normal_readable",
  "allowed_collapse_policies": ["never_before_commit", "may_disable_when_evidence_not_reachable"],
  "rule_bindings": [
    "erg.target.commit_gate.repo_min",
    "erg.evidence_before_commit.same_context_required",
    "erg.trust_boundary.visible_before_commit"
  ],
  "taxonomy_status": "v0_1_mandatory"
}
```

## 5.5 Anti-drift rules

Validators must reject:

```text
- ergonomic class IDs not in the frozen registry
- widget names used as ergonomic class names: modal, drawer, tab, accordion, card
- route-local class names
- free-text class labels used as authority
- multiple ergonomic classes mapped to the same component without declared precedence
- required UX projection refs with no ergonomic class mapping
```

The registry should live in `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py` as frozen `Literal[...]` values and exported as schema through `export_schema.py`, mirroring how `ux_governance.py` currently freezes `UXProjectionLaneRole`, `UXActionCluster`, `FROZEN_*` constants, and schema models.

# 6. Measurement provenance / admissibility model

This is the critical hardening.

The adjudicator must distinguish:

```text
known CSS geometry
physical-size estimate
visual-angle estimate
user-specific ergonomic preference
actual runtime conformance evidence
```

These are not interchangeable.

## 6.1 Provenance states

Every measured or declared datum in `ux_ergonomic_case_envelope@1` must use one of these states:

| State                       | Meaning                                                            | General admissibility                                                              |
| --------------------------- | ------------------------------------------------------------------ | ---------------------------------------------------------------------------------- |
| `measured_runtime`          | Captured from browser/runtime/test harness for this case.          | Strongest for CSS geometry and conformance.                                        |
| `declared_case`             | Supplied by reasoning model/user/operator for planned case.        | Admissible for planning; requires measurement obligation for implementation.       |
| `declared_user_profile`     | User-stated preference or limitation.                              | Admissible as user preference/profile; not clinical proof.                         |
| `verified_device_inventory` | Known hardware/display record with stable source.                  | May support physical estimates if scale chain is complete.                         |
| `inferred_heuristic`        | Derived from device class, window mode, task posture, or defaults. | Advisory/sensitivity only unless rulebook explicitly allows conservative fallback. |
| `unknown`                   | Not available.                                                     | Blocks dependent computations.                                                     |

## 6.2 Measured value shape

Every datum should use a wrapper:

```json
{
  "value": 720,
  "unit": "css_px",
  "provenance_state": "measured_runtime",
  "source_kind": "browser_visual_viewport",
  "source_ref": "playwright:artifact_inspector_reference_main:case_quarter_screen",
  "admissibility": "css_geometry_admissible",
  "ambiguity_severity": "none"
}
```

## 6.3 Admissibility levels

Use explicit levels:

```text
none
  no dependent computation allowed

css_geometry_admissible
  column count, panel CSS width, target CSS px, font CSS px checks allowed

planning_declared_css_geometry
  planning computation allowed; implementation must later measure

physical_size_admissible
  mm estimates allowed

visual_angle_admissible
  arcmin/degree estimates allowed

runtime_conformance_admissible
  implementation conformance judgment allowed
```

## 6.4 Datum-by-datum rules

| Datum                        | Required for                                                        | Admissible states                                            | Unknown fallback                                                                 |
| ---------------------------- | ------------------------------------------------------------------- | ------------------------------------------------------------ | -------------------------------------------------------------------------------- |
| `viewport_css_px`            | Candidate geometry, columns, CSS panel ranges                       | `measured_runtime`, `declared_case`                          | No preferred projection; result becomes `needs_review`.                          |
| `available_surface_css_px`   | Actual workbench feasibility                                        | `measured_runtime`, `declared_case`                          | No pass; at most `needs_review`.                                                 |
| `visual_viewport_css_px`     | Mobile/pinch/occluded viewport distinction                          | `measured_runtime` preferred                                 | Use viewport only for planning; mark measurement obligation.                     |
| `browser_zoom_percent`       | Physical-size chain only                                            | `measured_runtime`, `declared_case`                          | CSS geometry still allowed; mm/angle not allowed.                                |
| `os_scaling_percent`         | Physical-size chain only                                            | `verified_device_inventory`, `declared_case`                 | CSS geometry still allowed; mm/angle not allowed.                                |
| `device_pixel_ratio`         | Screenshot/rendering sanity, canvas scaling, physical chain support | `measured_runtime`                                           | Never enough alone for mm/angle.                                                 |
| `physical_ppi`               | Physical-size chain                                                 | `verified_device_inventory`, `declared_case`                 | No mm/angle.                                                                     |
| `css_px_to_mm_calibration`   | Physical-size chain                                                 | `measured_runtime`, `verified_device_inventory`              | No mm/angle.                                                                     |
| `viewing_distance_cm`        | Visual-angle computation                                            | `measured_runtime`, `declared_case`, `declared_user_profile` | No visual angle; use CSS fallback and mark ambiguity.                            |
| `user_acuity_scale`          | User-specific text/target inflation                                 | `declared_user_profile`                                      | Standard floor only; mark ambiguity if task is long-read/high-risk.              |
| `contrast_sensitivity_class` | Contrast/readability inflation                                      | `declared_user_profile`                                      | Use standard contrast floor; mark ambiguity.                                     |
| `input_mode`                 | Target-size floor                                                   | `measured_runtime`, `declared_case`                          | Use conservative hybrid/coarse floor; `needs_review` if high-risk action exists. |
| `task_posture`               | Density/readability policy                                          | `declared_case`                                              | Request is underspecified; `needs_review`.                                       |

The VisualViewport API can represent the visual viewport for a window, which makes it useful as a measured CSS geometry source. Device pixel ratio, however, is only the ratio of physical pixels to CSS pixels and is explicitly not available uniformly across all widely used browsers; it must not be treated as physical-size authority by itself. ([MDN Web Docs ][3])

## 6.5 Physical-size admissibility

Physical-size / mm estimates are admissible only if one of these is true:

```text
A. css_px_to_mm_calibration is measured for this runtime/device case

or

B. all of the following are available:
   - physical_ppi from verified_device_inventory or declared_case
   - device_pixel_ratio from measured_runtime
   - browser_zoom_percent known or explicitly declared not needed by calibration method
   - os_scaling_percent known or explicitly declared not needed by calibration method
   - rulebook marks the chain as admissible
```

DPR alone is never enough.

Physical PPI alone is never enough.

Viewport width in CSS px is never enough.

If physical-size chain is incomplete:

```text
- do not compute mm
- do not compute visual angle
- keep CSS px target/text floors
- emit ambiguity marker:
  ERG_AMBIG_PHYSICAL_SIZE_INADMISSIBLE
```

## 6.6 Visual-angle admissibility

Visual-angle estimates are admissible only if:

```text
physical_size_admissible == true
and viewing_distance_cm is measured_runtime or declared_case
```

If viewing distance is only `inferred_heuristic`, visual angle may be included in `sensitivity_report` but not used for pass/fail.

If user acuity is declared reduced but viewing distance or physical-size chain is missing:

```text
overall_judgment = needs_review
```

unless the adjudicator can satisfy a repo-local conservative fallback that is explicitly marked hard enough for the case.

## 6.7 Conservative fallback behavior

Required fallbacks:

```text
unknown physical PPI:
  use CSS px standards/presets only; no mm/angle

unknown browser zoom:
  CSS geometry still admissible if measured viewport exists;
  physical chain blocked

unknown OS scaling:
  CSS geometry still admissible if measured viewport exists;
  physical chain blocked

unknown viewing distance:
  no visual angle;
  use default CSS text floors;
  needs_review if reduced acuity, long_read, or high_precision_action posture

unknown user acuity:
  standard user profile;
  ambiguity advisory for ordinary editing;
  needs_review for long_read or if user profile explicitly says reduced but scale missing

unknown input mode:
  use stricter hybrid/coarse target floor;
  needs_review if commit/destructive/high-risk action is present

unknown available surface:
  no preferred projection;
  needs_review

candidate has only screenshot/image:
  not admissible;
  fail request validation or mark candidate underspecified
```

# 7. Judgment and preference semantics

## 7.1 Judgment values

Keep:

```text
pass
needs_review
fail
```

but make them deterministic.

## 7.2 `fail`

`overall_judgment = fail` when any of these holds:

```text
- any constitutional invariant is violated
- any ADEU deontic hard rule is violated
- any adopted external standard hard floor is violated by all available candidates
- authority stack illegal override is attempted
- no candidate projection is lawful and feasible
- candidate mints region/lane/action/state semantics not present upstream
- required evidence is not same-context reachable before commit
- trust boundary visibility is lost where required
- commit/destructive gate is not targetable or gated
- component visibility contract is missing for constitutional components
- selected/preferred projection is blocked
```

Blocked candidates alone do not force result fail if at least one lawful candidate remains. They are expected output.

## 7.3 `needs_review`

`overall_judgment = needs_review` when no hard fail exists, but any of these holds:

```text
- required CSS geometry is declared_case rather than measured_runtime for an implementation conformance context
- viewport/available surface is missing but coarse reasoning was still possible
- physical-size or visual-angle computation was requested but inadmissible
- user profile says reduced acuity/contrast sensitivity but lacks usable scale
- input mode is unknown and high-risk actions exist
- task posture is unknown
- candidate is structurally lawful but key ergonomic class mapping is incomplete
- ambiguity marker severity is review or blocking-but-not-fail
- two or more feasible candidates are equivalent at the preference tier and reasoning model must choose
```

## 7.4 `pass`

`overall_judgment = pass` only when:

```text
- at least one candidate projection is lawful and feasible
- every constitutional and deontic hard constraint is preserved
- all mandatory component ergonomic classes are mapped
- all required computations use admissible measurements for the adjudication phase
- no review-grade ambiguity remains
- preferred projection tier is determinable
```

Advisory ambiguity may remain under `pass`, but it must be explicitly listed.

## 7.5 Ambiguity severity

Add typed ambiguity severities:

```text
advisory
  does not affect judgment

review
  forces needs_review

blocking
  forces fail if it prevents hard-rule evaluation;
  otherwise forces needs_review with no preferred projection
```

Example:

```json
{
  "marker_id": "ERG_AMBIG_PHYSICAL_SIZE_INADMISSIBLE",
  "severity": "advisory",
  "affected_computations": ["mm_estimate", "visual_angle_estimate"],
  "judgment_effect": "no_effect_because_css_px_floors_sufficient"
}
```

## 7.6 Preference output: remove scalar scores in v0.1

Do not export decimal scores in v0.1.

Use ordinal/banded semantics:

```text
blocked
discouraged
marginal
acceptable
preferred
```

Candidate evaluation shape:

```json
{
  "candidate_profile_id": "artifact_inspector_quarter_screen_inspector_safe_buffered",
  "evaluation_status": "allowed",
  "preference_tier": "acceptable",
  "ordinal_group": 2,
  "preference_basis": [
    "preserves_status_and_trust_pins",
    "requires_evidence_collapse_with_summary",
    "lower_monitoring_continuity_than_split_pane"
  ],
  "hard_constraints_satisfied": [
    "evidence_before_commit_visibility",
    "trust_boundary_clarity",
    "commit_gate_target_floor"
  ],
  "remaining_ambiguity_marker_ids": [
    "ERG_AMBIG_PHYSICAL_SIZE_INADMISSIBLE"
  ]
}
```

Scalar scores may exist internally later, but they should not appear in `ux_ergonomic_adjudication_result@1`. This prevents a model or implementer from treating `0.81` as real measurement precision.

# 8. Exact v0.1 slice bundle

## 8.1 New module boundary

Add:

```text
packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py
```

Do not put the new models into `ux_governance.py`; that file already carries the V36 UX governance family. The ergonomic adjudicator should import existing UX governance types where useful, but remain a distinct module.

Optional later evidence module:

```text
packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics_evidence.py
```

Do not add this until runtime measurement evidence is actually materialized.

## 8.2 New schemas

Authoritative schemas:

```text
packages/adeu_core_ir/schema/ux_ergonomic_rule_authority_stack.v1.json
packages/adeu_core_ir/schema/ux_component_ergonomic_registry.v1.json
packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json
packages/adeu_core_ir/schema/ux_candidate_projection_profile_table.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_case_envelope.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_adjudication_request.v1.json
packages/adeu_core_ir/schema/ux_ergonomic_adjudication_result.v1.json
```

Spec mirrors:

```text
spec/ux_ergonomic_rule_authority_stack.schema.json
spec/ux_component_ergonomic_registry.schema.json
spec/ux_component_visibility_contract.schema.json
spec/ux_candidate_projection_profile_table.schema.json
spec/ux_ergonomic_case_envelope.schema.json
spec/ux_ergonomic_adjudication_request.schema.json
spec/ux_ergonomic_adjudication_result.schema.json
```

Update:

```text
packages/adeu_core_ir/src/adeu_core_ir/export_schema.py
packages/adeu_core_ir/src/adeu_core_ir/__init__.py
packages/adeu_core_ir/tests/test_ux_governance_export_schema.py
```

The export test currently asserts schema constants by filename; the seven new filenames must be added to that expected map.

## 8.3 Fixture family

Current repo has UX governance through `vnext_plus65` and assessments through `vNEXT_PLUS184`. Use the next slice as:

```text
apps/api/fixtures/ux_ergonomics/vnext_plus185/
```

Reference fixtures:

```text
ux_ergonomic_rule_authority_stack_reference.json
ux_component_ergonomic_registry_artifact_inspector_reference.json
ux_component_visibility_contract_artifact_inspector_reference.json
ux_candidate_projection_profile_table_artifact_inspector_reference.json
ux_ergonomic_case_envelope_desktop_maximized_reference.json
ux_ergonomic_case_envelope_quarter_screen_reference.json
ux_ergonomic_adjudication_request_artifact_inspector_desktop_reference.json
ux_ergonomic_adjudication_result_artifact_inspector_desktop_reference.json
ux_ergonomic_adjudication_request_artifact_inspector_quarter_screen_reference.json
ux_ergonomic_adjudication_result_artifact_inspector_quarter_screen_reference.json
```

Reject fixtures:

```text
ux_ergonomic_reject_platform_preset_overrides_constitutional.json
ux_ergonomic_reject_user_preference_lowers_hard_floor.json
ux_ergonomic_reject_candidate_mints_unknown_lane.json
ux_ergonomic_reject_candidate_without_visibility_contract.json
ux_ergonomic_reject_component_class_outside_registry.json
ux_ergonomic_reject_visual_angle_from_dpr_only.json
ux_ergonomic_reject_image_only_candidate_authority.json
ux_ergonomic_reject_scalar_preference_score_export.json
```

Optional evidence input later:

```text
artifacts/agent_harness/v185/evidence_inputs/ux_ergonomic_adjudication_evidence_v185.json
```

## 8.4 Tests

Add:

```text
packages/adeu_core_ir/tests/test_ux_ergonomics.py
packages/adeu_core_ir/tests/test_ux_ergonomics_admissibility.py
```

Core test responsibilities:

```text
test_reference_fixtures_validate_and_bind_to_existing_ux_governance_stack
test_canonicalize_ergonomic_artifacts_round_trip_without_drift
test_rule_authority_rejects_illegal_override
test_candidate_table_rejects_unknown_lane_or_action_cluster
test_component_registry_rejects_unknown_class
test_visibility_contract_requires_constitutional_components
test_measurement_model_rejects_visual_angle_from_dpr_only
test_unknown_available_surface_forces_needs_review
test_result_rejects_scalar_preference_score
test_result_judgment_derivation_matches_findings_and_ambiguity
```

## 8.5 Validator responsibilities

Implement canonicalization helpers:

```text
canonicalize_ux_ergonomic_rule_authority_stack_payload
canonicalize_ux_component_ergonomic_registry_payload
canonicalize_ux_component_visibility_contract_payload
canonicalize_ux_candidate_projection_profile_table_payload
canonicalize_ux_ergonomic_case_envelope_payload
canonicalize_ux_ergonomic_adjudication_request_payload
canonicalize_ux_ergonomic_adjudication_result_payload
```

Implement bundle checks:

```text
assert_ux_ergonomic_source_binding_consistent(...)
  verifies reference_surface_family/reference_instance_id across source UX artifacts

assert_ux_candidate_projection_table_bound_to_morph_ir(...)
  verifies candidate approved_profile_id and morph-axis legality

assert_ux_component_visibility_contract_complete(...)
  verifies every constitutional evidence/status/trust/commit component is classified

derive_ux_ergonomic_measurement_admissibility(...)
  derives css/physical/visual admissibility from provenance fields

derive_ux_ergonomic_overall_judgment(...)
  fail > needs_review > pass aggregation

assert_ux_ergonomic_result_consistent(...)
  verifies no scalar scores, no illegal preference elevation, blocked candidate reasons present
```

# 9. New failure modes introduced by these hardenings

## 9.1 Rulebook fossilization

A frozen rulebook can go stale as standards/platform guidance changes.

Guardrail:

```text
every external rule has source_ref, rulebook_version, adopted_by_repo_policy, and review cadence
```

## 9.2 Registry ossification

A finite registry can become too artifact-inspector-specific.

Guardrail:

```text
separate v0_1_mandatory classes from reserved/deferred classes;
new class requires schema/registry update, not route-local improvisation
```

## 9.3 Measurement bureaucracy

Strict admissibility can push too many cases to `needs_review`.

Guardrail:

```text
make CSS geometry useful without physical estimates;
block only dependent mm/visual-angle computations, not all adjudication
```

## 9.4 Platform-preset laundering

A platform preset could be treated as if it were constitutional law.

Guardrail:

```text
platform presets are default_preset unless adopted_by_repo_policy=true
```

## 9.5 User-preference laundering

A user preference such as “compact mode” could be used to suppress evidence or targets.

Guardrail:

```text
user preference may raise comfort constraints but may not lower hard floors or deontic visibility
```

## 9.6 Candidate-shape overfitting

Fixed candidate profiles may overfit the first artifact-inspector family.

Guardrail:

```text
candidate profile table is surface-family scoped;
other surface families get their own tables rather than open-ended candidate prose
```

## 9.7 Ordinal tier misuse

A downstream implementer may treat `preferred` as final design authority.

Guardrail:

```text
result says preferred_within_adjudicator_scope;
reasoning model must still emit selected_projection_decision
```

## 9.8 Structured false confidence

A structured physical estimate can look more reliable than it is.

Guardrail:

```text
physical_size_admissible and visual_angle_admissible are explicit booleans;
DPR-only estimates are rejected
```

# 10. Final recommendation

Implement v0.1 as a **schema-and-validator slice**, not as a visual/layout solver.

The first implementation should add:

```text
1. ux_ergonomics.py
2. seven schema artifacts
3. fixture family under apps/api/fixtures/ux_ergonomics/vnext_plus185/
4. canonicalization helpers
5. source-binding validators
6. authority-stack validators
7. candidate-profile validators
8. component-registry validators
9. measurement-admissibility derivation
10. judgment derivation with banded preference only
```

The key hardening rule is:

```text
No hidden rules.
No free-form candidates.
No unregistered component classes.
No physical/visual estimates from inadmissible measurements.
No scalar preference scores.
No override of constitutional or ADEU deontic law.
```

That turns the Ergonomic Instantiation Adjudicator from a strong architecture note into an implementation-safe first slice.

[1]: https://www.w3.org/WAI/WCAG22/Understanding/target-size-minimum.html?utm_source=chatgpt.com "Understanding SC 2.5.8: Target Size (Minimum) (Level AA)"
[2]: https://developer.apple.com/design/human-interface-guidelines/buttons?utm_source=chatgpt.com "Buttons | Apple Developer Documentation"
[3]: https://developer.mozilla.org/en-US/docs/Web/API/VisualViewport?utm_source=chatgpt.com "VisualViewport - Web APIs | MDN"
