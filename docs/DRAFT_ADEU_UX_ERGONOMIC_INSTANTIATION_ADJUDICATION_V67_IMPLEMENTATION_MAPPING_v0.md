# Draft ADEU UX Ergonomic Instantiation Adjudication V67 Implementation Mapping v0

Status: support / implementation mapping record; `V67` is complete on `main`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned `V67`
family into likely package, schema, validator, and fixture work so the family is
concrete before a starter lock is drafted.
That planned `V67-A` / `V67-B` / `V67-C` ladder is now shipped on `main`; the
mapping remains as family record and should not be read as authority to widen
the closed family.

## 1. Family Intent

`V67` should add ergonomic instantiation adjudication without treating that as:

- a reopening of the released UX governance stack;
- a free-form layout-solver lane;
- a screenshot-first design-assistant lane; or
- a runtime personalization engine by default.

So the implementation target is:

- explicit ergonomic rule authority;
- explicit frozen ergonomic taxonomy;
- explicit finite candidate projection profiles;
- explicit measurement provenance and admissibility;
- explicit adjudication request/result surfaces.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_core_ir`
  - models, enums, canonicalization helpers, validators, and schemas for the
    ergonomic family
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/ux_ergonomics/vnext_plus185/`
  - reference fixtures and reject fixtures for the first bounded slice.

Possible later secondary ownership:

- deterministic compiler/orchestrator package for `V67-B` adjudication logic,
  once the family moves beyond schema-and-validator posture.

The second support note’s proposed file placement is sound:

- `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py`
- exported schemas beside the current `ux_governance` schemas.

Expected starter implementation surfaces:

- `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py`
- `packages/adeu_core_ir/src/adeu_core_ir/__init__.py`
- `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- `packages/adeu_core_ir/tests/test_ux_ergonomics.py`
- `packages/adeu_core_ir/tests/test_ux_ergonomics_admissibility.py`
- `packages/adeu_core_ir/tests/test_ux_ergonomics_export_schema.py`

Expected export obligations:

- new authoritative schemas under:
  - `packages/adeu_core_ir/schema/ux_ergonomic_rule_authority_stack.v1.json`
  - `packages/adeu_core_ir/schema/ux_component_ergonomic_registry.v1.json`
  - `packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json`
  - `packages/adeu_core_ir/schema/ux_ergonomic_candidate_projection_profile_table.v1.json`
  - `packages/adeu_core_ir/schema/ux_ergonomic_case_envelope.v1.json`
  - `packages/adeu_core_ir/schema/ux_ergonomic_adjudication_request.v1.json`
  - `packages/adeu_core_ir/schema/ux_ergonomic_adjudication_result.v1.json`
- mirrored exports under:
  - `spec/ux_ergonomic_rule_authority_stack.schema.json`
  - `spec/ux_component_ergonomic_registry.schema.json`
  - `spec/ux_component_visibility_contract.schema.json`
  - `spec/ux_ergonomic_candidate_projection_profile_table.schema.json`
  - `spec/ux_ergonomic_case_envelope.schema.json`
  - `spec/ux_ergonomic_adjudication_request.schema.json`
  - `spec/ux_ergonomic_adjudication_result.schema.json`
- parity checks either by extending the current broad export-schema test or by
  adding an equivalently strict ergonomic export-schema test.

## 3. Candidate `V67` Artifact Set

Planning-level candidate outputs:

| Artifact | Likely slice | Role |
|---|---|---|
| `ux_ergonomic_rule_authority_stack@1` | `V67-A` | rulebook, precedence, override posture, provenance |
| `ux_component_ergonomic_registry@1` | `V67-A` | frozen ergonomic class vocabulary |
| `ux_component_visibility_contract@1` | `V67-A` | maps semantic surface parts into ergonomic classes and visibility duties |
| `ux_ergonomic_candidate_projection_profile_table@1` | `V67-A` | finite candidate projection set for ergonomic evaluation |
| `ux_ergonomic_case_envelope@1` | `V67-A` | case envelope plus measurement provenance / admissibility |
| `ux_ergonomic_adjudication_request@1` | `V67-A` | bounded request over consumed constitutional basis plus candidate set |
| `ux_ergonomic_adjudication_result@1` | `V67-A` | bounded adjudication output with blocked candidates, tiers, ambiguity, obligations |

`V67-A` should ship all seven surfaces, but as a schema-and-validator slice rather
than a full adjudication solver.

If `V67-C` selects replayable advisory bridge output rather than helper-only
comparison, the bounded later surfaces should be:

| Artifact | Likely slice | Role |
|---|---|---|
| `ux_ergonomic_runtime_measurement_evidence@1` | `V67-C` | typed realized runtime measurement rows bound to adjudication lineage |
| `ux_ergonomic_runtime_bridge_report@1` | `V67-C` | non-sovereign advisory drift / incompleteness report over realized evidence |

## 4. `V67-A` Starter Mapping

### 4.1 Scope

`V67-A` should stay bounded to:

- schema definitions;
- model validators;
- canonicalization helpers;
- schema export;
- artifact-inspector-family anchored reference fixtures;
- reject fixtures for the most important failure seams.

Starter checks should explicitly harden:

- hidden ergonomic rules;
- free-form candidate projections;
- drifting component taxonomy;
- inadmissible physical / visual calculations;
- fake precision in pass/fail or preference output.

### 4.2 Consumed Basis

`V67-A` and `V67-B` should consume the required released UX governance basis only:

- `ux_domain_packet@1`
- `ux_morph_ir@1`
- `v36a_first_family_approved_profile_table@1`
- `v36a_same_context_reachability_glossary@1`
- `ux_surface_projection@1`
- `ux_interaction_contract@1`
- `ux_surface_compiler_variant_manifest@1`

Optional later-`V67-C` / downstream evidence basis only:

- `ux_morph_diagnostics@1`
- `ux_conformance_report@1`
- rendered / replay / runtime evidence artifacts where explicitly selected.

For the bounded starter, current repo binding should stay anchored to the existing
artifact-inspector references in:

- `apps/api/fixtures/ux_governance/vnext_plus61/`
- `apps/api/fixtures/ux_governance/vnext_plus62/`
- `apps/api/fixtures/ux_governance/vnext_plus65/`

Fixture numbering clarification:

- `apps/api/fixtures/ux_ergonomics/vnext_plus185/` follows the global next-arc /
  agent-harness event number, not the highest existing `apps/api` fixture
  directory number.

### 4.3 Required Starter Enumerations

Expected frozen starter enums:

- authority layers:
  - `constitutional_surface_invariant`
  - `repo_local_policy`
  - `external_standard_floor`
  - `platform_preset`
  - `user_declared_preference`
  - `heuristic_utility`
- rule force:
  - `hard_block`
  - `hard_floor`
  - `advisory_ranking`
- provenance states:
  - `measured_runtime`
  - `declared_case`
  - `declared_user_profile`
  - `verified_device_inventory`
  - `inferred_heuristic`
  - `unknown`
- admissibility levels:
  - `none`
  - `css_geometry_admissible`
  - `planning_declared_css_geometry`
  - `physical_size_admissible`
  - `visual_angle_admissible`
  - `runtime_conformance_admissible`
- adjudication preference tiers:
  - `blocked`
  - `discouraged`
  - `marginal`
  - `acceptable`
  - `preferred`
- overall judgment:
  - `pass`
  - `needs_review`
  - `fail`

The starter should avoid scalar exported preference scores.

### 4.4 Expected Source Binding Fields

Starter reference fixtures and starter-bound request/result artifacts should carry
at least:

- `reference_surface_family`
- `reference_instance_id`
- `approved_profile_id` where applicable
- `source_artifact_refs`
- `source_artifact_hashes`

For `V67-A`, source-artifact hashes should be required for the consumed released UX
governance artifacts in the reference fixture family. Missing hashes may be
tolerated only for non-authorizing planning examples, not for shipped starter
references.

### 4.5 Required Starter Validators

Validation taxonomy should stay explicit:

- local model validators
  - one artifact payload only
  - schema shape, closed enums, internal invariants, canonicalization
- bundle validators
  - cross-artifact binding to the consumed UX governance basis
  - source refs / hashes
  - same-context glossary binding
  - projection / approved-profile consistency
- admissibility derivation helpers
  - derive CSS / physical / visual / runtime admissibility from provenance fields
- judgment consistency helpers
  - ensure request/result coherence and reason-coded blocking posture

Rule-authority validators should reject:

- any lower layer trying to weaken a higher hard floor;
- any platform preset treated as hard law without explicit repo adoption;
- any user preference that lowers a hard minimum;
- any rule without explicit provenance.

Candidate-profile validators should reject:

- candidates that reference regions, lanes, action clusters, or states not present
  in the consumed constitutional basis;
- candidates that use same-context reveal terms not present in
  `v36a_same_context_reachability_glossary@1`;
- candidates that create new semantic authority;
- candidates that omit required visibility / collapse / reveal claims for required
  evidence, trust, status, or commit-bearing components;
- free-form or screenshot-only candidates.

Component-registry validators should reject:

- unknown ergonomic class IDs;
- widget terms used as ergonomic class names;
- incomplete mapping for required source-semantic kinds.

Measurement validators should reject:

- physical-size or visual-angle admissibility from DPR-only or otherwise incomplete
  chains;
- dependent computations when required provenance is `unknown`;
- runtime-conformance claims based only on planning-declared geometry.

Result validators should reject:

- decimal exported preference scores;
- blocked candidates without reason codes;
- admissible claims that exceed the supplied measurement chain;
- `overall_judgment` values that disagree with blocked / ambiguity posture.

Recommended helper / assertion split:

- `canonicalize_ux_ergonomic_rule_authority_stack_payload(...)`
- `canonicalize_ux_component_ergonomic_registry_payload(...)`
- `canonicalize_ux_component_visibility_contract_payload(...)`
- `canonicalize_ux_ergonomic_candidate_projection_profile_table_payload(...)`
- `canonicalize_ux_ergonomic_case_envelope_payload(...)`
- `canonicalize_ux_ergonomic_adjudication_request_payload(...)`
- `canonicalize_ux_ergonomic_adjudication_result_payload(...)`
- `assert_ux_ergonomic_bundle_source_binding_consistent(...)`
- `assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection(...)`
- `assert_ux_ergonomic_candidate_projection_table_bound_to_approved_profiles(...)`
- `assert_ux_visibility_contract_complete_for_projection(...)`
- `assert_ux_case_envelope_admissibility_consistent(...)`
- `assert_ux_adjudication_result_consistent_with_request(...)`

### 4.6 Likely Fixture Set

Bounded starter fixture family:

- `apps/api/fixtures/ux_ergonomics/vnext_plus185/`

Reference fixtures should likely include:

- rule-authority stack reference
- component ergonomic registry reference
- component visibility contract reference
- candidate projection profile table reference
- desktop maximized case envelope reference
- quarter-screen case envelope reference
- adjudication request / result references for those cases

Reject fixtures should likely include:

- candidate with unknown ergonomic class
- candidate with lane ref not present in consumed projection
- user preference lowering a hard floor
- visual-angle derivation from DPR-only chain
- exported result with decimal preference score
- candidate that hides evidence before commit without same-context reveal law.

### 4.7 Likely Tests

Expected starter tests:

- schema export parity for all seven artifacts;
- all seven schema constants and models export from `adeu_core_ir.__init__`;
- reference fixtures validate and bind to existing UX governance lineage;
- reject fixtures fail with stable reason codes;
- candidate table cannot reference unknown region / lane / action / state IDs;
- visibility contract covers all evidence / trust / status / commit-bearing parts of
  the projection;
- same-context reveal terms validate against
  `v36a_same_context_reachability_glossary@1`;
- authority-stack validators enforce precedence;
- component registry remains frozen and complete for the starter family;
- platform presets do not become hard law unless repo-adopted;
- user preferences cannot lower a hard floor;
- measurement admissibility derivation rejects inadmissible chains;
- adjudication result forbids scalar exported scores;
- cross-artifact source refs and hashes bind to the consumed UX governance basis.

## 5. Deferred To Later Slices

Deferred to `V67-B` or later:

- actual bounded candidate evaluation engine;
- finite candidate ranking over hard-pass candidates;
- deeper implementation measurement harvesting;
- screenshot/rendered-surface witness integration beyond consumed evidence refs;
- dynamic runtime personalization behavior.

`V67-A` should therefore be read as:

- schema-and-validator backbone only;
- not layout solving;
- not runtime adaptation.
