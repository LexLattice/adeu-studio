# Draft ADEU UX Ergonomic Instantiation Adjudication V67A Implementation Mapping v0

Status: support note for the planned `V67-A` starter implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how the starter
`V67-A` slice should widen from the released Morphic UX governance substrate into
one bounded ergonomic schema-and-validator backbone without reopening released UX
governance ownership, silently minting new surface semantics, deriving authority
from screenshots, or pretending to solve layout.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v52.md`
- `docs/ARCHITECTURE_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_UX_ERGONOMIC_INSTANTIATION_ADJUDICATION_V67_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/DRAFT_ERGONOMIC_INSTANTIATION_ADJUDICATOR_2ND_PASS_v0.md`
- `docs/support/REVIEW_GPTPRO_ERGONOMIC_INSTANTIATION_ADJUDICATOR_2ND_PASS_v0.md`

## Carry Forward Nearly As-Is

- the released UX governance basis only:
  - `ux_domain_packet@1`
  - `ux_morph_ir@1`
  - `v36a_first_family_approved_profile_table@1`
  - `v36a_same_context_reachability_glossary@1`
  - `ux_surface_projection@1`
  - `ux_interaction_contract@1`
  - `ux_surface_compiler_variant_manifest@1`
- optional later-`V67-C` evidence only:
  - `ux_morph_diagnostics@1`
  - `ux_conformance_report@1`
- the rule that constitutional invariants remain prior to ergonomic instantiation
- the rule that evidence-before-commit and trust-boundary law are consumed, not
  reminted here
- the rule that platform presets are not hard law unless explicitly repo-adopted
- the rule that user preference may raise but may not lower hard floors
- the rule that screenshots are witness only and not authority by themselves
- the rule that scalar exported preference scores are forbidden in the starter lane.

## Re-Author With Repo Alignment

Candidate new `V67-A` surfaces:

- `ux_ergonomic_rule_authority_stack@1`
- `ux_component_ergonomic_registry@1`
- `ux_component_visibility_contract@1`
- `ux_ergonomic_candidate_projection_profile_table@1`
- `ux_ergonomic_case_envelope@1`
- `ux_ergonomic_adjudication_request@1`
- `ux_ergonomic_adjudication_result@1`

Those starter surfaces should remain bounded to:

- one explicit rule-authority stack only
- one frozen ergonomic class vocabulary only
- one per-surface visibility-contract layer only
- one finite candidate-profile table only
- one provenance-bearing case-envelope model only
- one bounded request/result pair only
- one artifact-inspector-family anchor only in the first shipped fixture family.

They should decide only:

- what ergonomic rules exist here and in what precedence order;
- what ergonomic classes exist here and how a released surface maps into them;
- which candidate projection profiles are even admissible for evaluation;
- which measurement chains are admissible for CSS, physical, visual-angle, or
  runtime-conformance reasoning;
- how a bounded adjudication request/result is represented without layout solving.

They should keep:

- no general layout solver
- no runtime personalization engine
- no new regions / lanes / action clusters
- no new evidence-before-commit law
- no clinical user modeling
- no screenshot-first candidate admission
- no decimal exported preference scores
- no hiding of source refs or source hashes in starter reference fixtures.

## Starter Source Binding

`V67-A` reference fixtures and starter-bound request/result artifacts should carry at
least:

- `reference_surface_family`
- `reference_instance_id`
- `approved_profile_id` where applicable
- `source_artifact_refs`
- `source_artifact_hashes`

Starter candidate profiles should bind only to:

- released `ux_surface_projection@1` region / lane / action refs;
- released `ux_interaction_contract@1` semantic obligations;
- released `v36a_first_family_approved_profile_table@1` approved profile IDs;
- released `v36a_same_context_reachability_glossary@1` reveal vocabulary.

`source_artifact_hashes` should follow the repo-native reference shape:

```json
{
  "artifact_ref": "apps/api/fixtures/ux_governance/vnext_plus62/ux_surface_projection_artifact_inspector_reference.json",
  "artifact_hash": "<64-char lowercase sha256>"
}
```

Starter validation should require:

- repo-relative `artifact_ref`
- lowercase 64-character `artifact_hash`
- sorted unique rows by `artifact_ref`
- canonical hash match for shipped reference fixtures.

## Starter Validation Split

`V67-A` should keep local validation and bundle validation distinct.

### Local model validators

These validate one payload only:

- schema shape
- frozen enums
- internal field consistency
- canonicalization
- no free-text category drift

### Bundle validators

These validate cross-artifact relationships:

- source refs / hashes bind to the consumed UX governance basis
- candidate projection rows reference only released projection parts
- same-context reveal terms exist in the released glossary
- approved-profile IDs exist in the released approved-profile table
- visibility contract covers required evidence / trust / status / commit-bearing
  parts of the released surface projection
- request/result lineage stays consistent with the consumed basis.

### Admissibility helpers

These derive:

- CSS geometry admissibility
- physical-size admissibility
- visual-angle admissibility
- runtime-conformance admissibility

from explicit provenance states rather than ambient inference.

## Starter Schema And Constant Direction

The repo-native field name should be `schema`, not draft-only `schema_id`.

Expected constants:

- `UX_ERGONOMIC_RULE_AUTHORITY_STACK_SCHEMA = "ux_ergonomic_rule_authority_stack@1"`
- `UX_COMPONENT_ERGONOMIC_REGISTRY_SCHEMA = "ux_component_ergonomic_registry@1"`
- `UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA = "ux_component_visibility_contract@1"`
- `UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA = "ux_ergonomic_candidate_projection_profile_table@1"`
- `UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA = "ux_ergonomic_case_envelope@1"`
- `UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA = "ux_ergonomic_adjudication_request@1"`
- `UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA = "ux_ergonomic_adjudication_result@1"`

Expected authoritative schema files:

- `packages/adeu_core_ir/schema/ux_ergonomic_rule_authority_stack.v1.json`
- `packages/adeu_core_ir/schema/ux_component_ergonomic_registry.v1.json`
- `packages/adeu_core_ir/schema/ux_component_visibility_contract.v1.json`
- `packages/adeu_core_ir/schema/ux_ergonomic_candidate_projection_profile_table.v1.json`
- `packages/adeu_core_ir/schema/ux_ergonomic_case_envelope.v1.json`
- `packages/adeu_core_ir/schema/ux_ergonomic_adjudication_request.v1.json`
- `packages/adeu_core_ir/schema/ux_ergonomic_adjudication_result.v1.json`

Expected mirror schema files:

- `spec/ux_ergonomic_rule_authority_stack.schema.json`
- `spec/ux_component_ergonomic_registry.schema.json`
- `spec/ux_component_visibility_contract.schema.json`
- `spec/ux_ergonomic_candidate_projection_profile_table.schema.json`
- `spec/ux_ergonomic_case_envelope.schema.json`
- `spec/ux_ergonomic_adjudication_request.schema.json`
- `spec/ux_ergonomic_adjudication_result.schema.json`

## Mandatory Starter Ergonomic Vocabulary

`V67-A` should freeze the starter ergonomic class list exactly as:

- `erg_action_lane_container`
- `erg_work_context_lane`
- `erg_source_text_lane`
- `erg_evidence_lane`
- `erg_diagnostics_lane`
- `erg_status_surface`
- `erg_trust_boundary_surface`
- `erg_navigation_lane`
- `erg_advisory_action_cluster`
- `erg_comparison_action_cluster`
- `erg_commit_gate_action_cluster`

Recommended first artifact-inspector mapping:

- `lane:action-lane -> erg_action_lane_container`
- `lane:work-context-lane -> erg_work_context_lane`
- `lane:source-lane -> erg_source_text_lane`
- `lane:evidence-lane -> erg_evidence_lane`
- `lane:diagnostics-lane -> erg_diagnostics_lane`
- `lane:status-lane -> erg_status_surface`
- `lane:trust-boundary-lane -> erg_trust_boundary_surface`
- `lane:navigation-lane -> erg_navigation_lane`
- `action_cluster:advisory-actions -> erg_advisory_action_cluster`
- `action_cluster:comparison-actions -> erg_comparison_action_cluster`
- `action_cluster:commit-actions -> erg_commit_gate_action_cluster`

## Starter Candidate Profile Set

The starter candidate table should freeze the first candidate rows as:

- `artifact_inspector_maximized_split_reference`
- `artifact_inspector_half_screen_split_reference`
- `artifact_inspector_narrow_stacked_same_context`
- `artifact_inspector_quarter_screen_inspector_safe_buffered`

## Starter Field Direction

Minimum `ux_ergonomic_rule_authority_stack@1` direction:

- `schema`
- `rule_stack_id`
- `rules`
- each rule carries:
  - `rule_id`
  - `authority_layer`
  - `force`
  - `source_kind`
  - `source_ref`
  - `adopted_by_repo_policy`
  - `applies_to`
  - `constraint`
  - `override_policy`
  - `provenance`

Minimum `ux_component_ergonomic_registry@1` direction:

- `schema`
- `registry_id`
- `registry_version`
- `class_rows`
- each class row carries:
  - `class_id`
  - `applies_to_surface_units`
  - `allowed_source_semantic_kinds`
  - `default_visibility_requirement`
  - `default_targetability_requirement`
  - `default_readability_requirement`
  - `allowed_collapse_policies`
  - `rule_bindings`
  - `taxonomy_status`

Minimum `ux_component_visibility_contract@1` direction:

- `schema`
- `contract_id`
- `reference_surface_family`
- `reference_instance_id`
- `source_artifact_refs`
- `source_artifact_hashes`
- `component_rows`
- each component row carries:
  - `component_ref`
  - `semantic_kind`
  - `ergonomic_class_id`
  - `visibility_state`
  - `collapse_policy`
  - `reveal_transition_or_none`
  - `continuous_visibility_required`

Minimum `ux_ergonomic_candidate_projection_profile_table@1` direction:

- `schema`
- `candidate_profile_table_id`
- `reference_surface_family`
- `reference_instance_id`
- `source_artifact_refs`
- `source_artifact_hashes`
- `candidate_rows`
- each candidate row carries:
  - `candidate_profile_id`
  - `approved_profile_id`
  - `target_envelope`
  - `projection_shape`
  - `component_visibility_claims`
  - `action_targeting_claims`
  - `free_aesthetic_variables_declared`

Minimum `ux_ergonomic_case_envelope@1` direction:

- `schema`
- `case_envelope_id`
- `reference_surface_family`
- `window_occupancy_mode`
- `input_mode`
- `task_posture`
- provenance-bearing measured / declared value wrappers for:
  - viewport CSS geometry
  - available surface CSS geometry
  - zoom / scaling where present
  - device / PPI / calibration where present
  - viewing distance where present
  - user ergonomic preference fields where present

Minimum `ux_ergonomic_adjudication_request@1` direction:

- `schema`
- `request_id`
- `reference_surface_family`
- `reference_instance_id`
- `source_artifact_refs`
- `source_artifact_hashes`
- `rule_stack_ref`
- `registry_ref`
- `visibility_contract_ref`
- `candidate_profile_table_ref`
- `case_envelope_ref`

Minimum `ux_ergonomic_adjudication_result@1` direction:

- `schema`
- `result_id`
- `request_ref`
- `source_artifact_refs`
- `source_artifact_hashes`
- `report_status`
- `overall_judgment`
- `blocked_candidate_rows`
- `feasible_candidate_rows`
- `ambiguity_rows`
- `measurement_obligation_rows`

Starter `report_status` should remain artifact-validity-only:

- `valid`
- `invalid_request_basis_mismatch`
- `invalid_candidate_table_basis_mismatch`
- `invalid_visibility_contract_basis_mismatch`
- `invalid_case_envelope_admissibility`
- `invalid_unknown_candidate_ref`

Starter `overall_judgment` should remain ergonomic-outcome-only:

- `pass`
- `needs_review`
- `fail`

Starter preference tiers only:

- `blocked`
- `discouraged`
- `marginal`
- `acceptable`
- `preferred`

`V67-A` reference result fixtures are schema / validator fixtures only. They are
not engine-computed ergonomic adjudications. `V67-A` may validate internal
consistency, source binding, reason-code shape, and forbidden scalar-score
absence, but it may not claim to evaluate candidate feasibility.

## Do Not Import

- actual candidate evaluation / ranking logic beyond starter consistency checks
- runtime measurement harvesting
- adaptive runtime morph switching
- screenshot witness integration beyond explicit source refs
- platform guidance treated as hard law by default
- prose-only candidate admission
- scalar ergonomic scoring
- new generic UX semantic families outside the bounded ergonomic lane.

## Likely Implementation Surfaces

- `packages/adeu_core_ir/src/adeu_core_ir/ux_ergonomics.py`
- `packages/adeu_core_ir/src/adeu_core_ir/__init__.py`
- `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- `packages/adeu_core_ir/schema/*.v1.json`
- `spec/*.schema.json`
- `packages/adeu_core_ir/tests/test_ux_ergonomics.py`
- `packages/adeu_core_ir/tests/test_ux_ergonomics_admissibility.py`
- `packages/adeu_core_ir/tests/test_ux_ergonomics_export_schema.py`
- `apps/api/fixtures/ux_ergonomics/vnext_plus185/`

Fixture numbering note:

- `apps/api/fixtures/ux_ergonomics/vnext_plus185/` follows the global next-arc /
  agent-harness event number, not the highest existing `apps/api` fixture
  directory number.

## Starter Acceptance Shape

`V67-A` is ready to lock only when the planned starter can plausibly satisfy:

- all seven schemas export cleanly
- all seven models export from `adeu_core_ir.__init__`
- reference fixtures validate locally
- reject fixtures fail with stable reason categories
- same-context reveal terms validate against the released glossary
- platform presets do not become hard law unless repo-adopted
- user preferences cannot lower hard floors
- DPR-only chains cannot authorize physical-size or visual-angle claims
- results cannot export decimal preference scores
- cross-artifact source refs and hashes bind to the released UX governance basis.
