# Locked Continuation vNext+65 (Draft Lock)

This document drafts the next arc after:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md`
- `docs/ASSESSMENT_vNEXT_PLUS61_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md`
- `docs/ASSESSMENT_vNEXT_PLUS62_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md`
- `docs/ASSESSMENT_vNEXT_PLUS63_EDGES.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md`
- `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md`
- `docs/ASSESSMENT_vNEXT_PLUS64_EDGES.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md`
- `docs/seed arc v10.md`
- `docs/DRAFT_CLOSEOUT_HARDENING_BUNDLE_v0.md`
- `docs/FUTURE_CLEANUPS.md`
- `docs/SEMANTICS_v3.md`
- `docs/ARCHITECTURE_ADEU_SEMANTIC_COMPILER_v0.md`

Status: draft lock (not frozen yet, March 15, 2026 UTC).

## Decision Basis

- `vNext+64` (`V36-D`, `D1`/`D2`) is merged on `main` with green CI checks.
- `vNext+64` closeout decision capture is recorded in
  `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md` with `all_passed = true`.
- `docs/ASSESSMENT_vNEXT_PLUS64_EDGES.md` marks the `V36-D` diagnostics/conformance edge
  set as closed and restores eligibility for the next thin `V36` path.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` now names `V36-E` as the next default candidate
  after `V36-D` closure.
- current repo reality is narrower than a broad multi-product compiler lane:
  - canonical `ux_domain_packet@1`, canonical `ux_morph_ir@1`, one accepted bound
    `V36-A` reference pair, the first-family approved profile table, and the
    same-context reachability glossary exist on `main`,
  - canonical `ux_surface_projection@1`, canonical `ux_interaction_contract@1`, one
    accepted bound `V36-B` reference pair, explicit authority provenance, stable
    provenance hooks, and stable implementation-observable bindings exist on `main`,
  - one bounded rendered `artifact_inspector_advisory_workbench` route, one rendered
    route contract, one semantic snapshot, one implementation binding manifest, and
    canonical `v36c_artifact_inspector_reference_surface_evidence@1` exist on `main`,
  - canonical `ux_morph_diagnostics@1`, canonical `ux_conformance_report@1`, one
    accepted diagnostics artifact, one accepted conformance report, and canonical
    `v36d_morph_diagnostics_conformance_evidence@1` now exist on `main`,
  - no released `ux_surface_compiler_export@1` artifact family exists on `main`,
  - no released bounded lawful variant export lane exists on `main`.
- `vNext+65` therefore selects one thin `V36-E` baseline slice only:
  - canonical deterministic compiler export for the bounded
    `artifact_inspector_advisory_workbench` family over the released `V36-A` / `V36-B` /
    `V36-C` / `V36-D` substrate,
  - exactly one canonical reference export plus one explicitly approved alternate lawful
    export bound to the frozen two-profile table,
  - the alternate lawful export must receive its own deterministic diagnostics and
    conformance evaluation under the frozen `V36-D` conformance-report structure and
    aggregation rule before emission,
  - closeout evidence plus determinism/guard coverage,
  - no broad route-family compiler rollout, no profile-count widening, no runtime
    auto-repair, and no repo-wide route rewrite in this arc.

## Global Locks

- `docs/SEMANTICS_v3.md` remains authoritative for runtime behavior.
- No solver/runtime semantics contract changes are authorized in this arc.
- `docs/LOCKED_INSTRUCTION_KERNEL_v0.md` and
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` through
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md` remain authoritative for baseline
  continuity.
- Determinism and replayability remain mandatory for all tooling outputs and tests.
- Canonical JSON and hashing profile remain frozen and unchanged.
- Stop-gate schema-family continuity remains frozen:
  - `stop_gate_metrics@1` only; no schema-family fork in this arc.
- Stop-gate metric-key continuity remains frozen:
  - no new metric keys are introduced in v65,
  - v65 keyset must be exactly equal to v64 keyset,
  - baseline derived cardinality at v65 start is `80` and must remain unchanged in this
    arc.
- Provider/proposer surface continuity remains frozen:
  - no provider expansion,
  - no proposer endpoint expansion in this arc.
- Boundary-release scope lock for v65 is explicit and narrow:
  - this arc authorizes one bounded `L1` compiler-export substrate lane plus its
    closeout evidence lane only,
  - no `L2` broad compiler rollout or multi-family variant release is authorized in this
    arc,
  - no worker direct user-boundary release is authorized in this arc,
  - no new governance authority, acceptance authority, or closeout authority surface is
    released beyond the closed `V35` baseline,
  - no repo-wide route-rewrite authority is authorized in this arc.
- `V35-A` through `V35-E` runtime/state/delegation/visibility/topology/enforcement
  surfaces remain frozen prerequisites and are not redefined by this arc.
- `V36-A`, `V36-B`, `V36-C`, and `V36-D` surfaces remain frozen prerequisites and are not
  redefined by this arc.
- `V36-E` release-shape lock for v65 is frozen:
  - this arc is one bounded surface-compiler export and controlled lawful-variant
    baseline only,
  - the arc must consume released `V36-A`, `V36-B`, `V36-C`, and `V36-D` artifacts rather
    than redefining them,
  - the emitted compiler exports must remain bound to the same
    `reference_surface_family`, `reference_instance_id`, and `approved_profile_id` as the
    accepted `V36-A` pair, accepted `V36-B` pair, released `V36-C` route, and accepted
    `V36-D` diagnostics/conformance artifacts,
  - exactly two approved profile ids are in scope for emitted exports:
    `artifact_inspector_reference` and `artifact_inspector_alternate`,
  - combinations outside the frozen `V36-A` approved profile table are invalid even if
    their axis values are individually allowed,
  - implementation exports must remain derived from canonical UX artifacts, not
    side-channel prompts, local route heuristics, or free-form brief interpretation at
    the last mile,
  - implementation exports may not rely on unconstrained CSS/theme overrides that weaken
    required salience, hide required evidence, or visually neutralize diagnostics or
    deontic boundaries,
  - no emitted profile may pass if its own deterministic consumed
    diagnostics/conformance evaluation under the frozen `V36-D` conformance-report
    structure and aggregation rule shows deontic, epistemic, trust-boundary, or
    profile-contract drift,
  - UI artifacts may express authority but may not mint authority; this arc may not
    weaken any accepted `V35` authority gate by export arrangement, implementation target
    mapping, or lawful-variant choice.

## Arc Scope (Draft Lock)

This arc proposes one thin-slice chunk with two implementation slices (one PR each):

1. `E1` Surface compiler export baseline (`V36-E`)
2. `E2` Surface compiler export evidence + determinism/guard suite (`V36-E`)

Out-of-scope note:

- any route-family or multi-surface compiler rollout in this arc,
- any profile-count widening beyond the frozen two-profile table in this arc,
- any morph-axis vocabulary widening or value-set widening in this arc,
- any repo-wide design-system, token, or theme overhaul in this arc,
- any runtime enforcement or runtime auto-repair change in this arc,
- the separate closeout-hardening bundle (`O1`/`O2`/`O3`) in this arc,
- provider/proposer surface expansion in this arc,
- solver/runtime semantics changes in this arc,
- stop-gate metric-key expansion or schema-family fork in this arc.

## Deferred Follow-On Candidates (Non-v65)

- separate operational closeout-hardening bundle:
  - `O1` closeout orchestration extraction
  - `O2` closeout artifact index + lint
  - `O3` advisory adjudication scaffold
- the Copilot/Codex CLI approval-flag UX cleanup remains deferred under
  `docs/FUTURE_CLEANUPS.md`

## V64 Continuity Consumption (Machine-Checkable)

```json
{
  "schema": "continuity_consumption@1",
  "source_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md",
  "target": "V36-E-baseline",
  "required_continuity_guards": [
    "V36_D_D1_MORPH_DIAGNOSTICS_CONFORMANCE_BASELINE_GREEN",
    "V36_D_D2_MORPH_DIAGNOSTICS_CONFORMANCE_EVIDENCE_GUARDS_GREEN"
  ],
  "expected_relation": "v64_v36d_diagnostics_and_conformance_remain_frozen_while_v36e_bounded_surface_compiler_exports_are_added"
}
```

Consumption lock:

- `continuity_consumption@1` is docs-authoritative continuity intent for v65.
- this narrowed machine-checkable consumption block is v64-local only and does not weaken
  the global continuity locks declared above; v14-v64 baseline continuity remains in
  force for the arc as a whole.
- duplicate values in `required_continuity_guards` are invalid and fail closed.

## V36-E Surface Compiler Export Contract (Machine-Checkable)

```json
{
  "schema": "v36e_surface_compiler_export_contract@1",
  "target_arc": "vNext+65",
  "target_path": "V36-E",
  "preserved_authority_inputs": {
    "options_baseline": "docs/DRAFT_NEXT_ARC_OPTIONS_v10.md",
    "seed_source_doc": "docs/seed arc v10.md",
    "v36a_domain_morph_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md#v36a_ux_domain_morph_ir_contract@1",
    "v36a_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md",
    "v36b_projection_interaction_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS62.md#v36b_surface_projection_interaction_contract@1",
    "v36b_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS62.md",
    "v36c_rendered_reference_surface_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS63.md#v36c_artifact_inspector_reference_surface_contract@1",
    "v36c_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS63.md",
    "v36d_diagnostics_conformance_contract": "docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md#v36d_morph_diagnostics_conformance_contract@1",
    "v36d_closeout_decision": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS64.md",
    "v35e_runtime_authority_baseline": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1",
    "bounded_reference_surface_family": "artifact_inspector_advisory_workbench",
    "stop_gate_schema_family": "stop_gate_metrics@1"
  },
  "compiler_export_requirements": {
    "foundation_status": "deterministic_surface_compiler_exports_over_released_v36a_v36b_v36c_v36d_substrate",
    "required_input_artifacts": [
      "ux_domain_packet@1",
      "ux_morph_ir@1",
      "v36a_accepted_reference_instance_pair@1",
      "v36a_first_family_approved_profile_table@1",
      "v36a_same_context_reachability_glossary@1",
      "ux_surface_projection@1",
      "ux_interaction_contract@1",
      "v36b_accepted_reference_pair@1",
      "v36c_rendered_reference_surface_contract@1",
      "v36c_rendered_reference_surface_semantic_snapshot@1",
      "v36c_rendered_reference_surface_binding_manifest@1",
      "ux_morph_diagnostics@1",
      "ux_conformance_report@1",
      "v36d_morph_diagnostics_conformance_evidence@1"
    ],
    "reference_surface_family": "artifact_inspector_advisory_workbench",
    "required_reference_binding_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id"
    ],
    "reference_binding_tuple_equality_across_v36a_v36b_v36c_v36d_v36e_required": true,
    "surface_compiler_export_schema_required": true,
    "surface_compiler_variant_manifest_schema_required": true,
    "canonical_profile_id": "artifact_inspector_reference",
    "alternate_profile_id": "artifact_inspector_alternate",
    "approved_profile_ids_must_exist_in_v36a_table": true,
    "approved_profile_cardinality_exact": 2,
    "out_of_table_profile_combinations_fail_closed": true,
    "surface_compiler_export_required_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id",
      "source_artifact_refs",
      "implementation_target_payloads",
      "exported_provenance_hook_map",
      "exported_implementation_binding_map",
      "conformance_gating_ref",
      "derivation_metadata"
    ],
    "surface_compiler_variant_manifest_required_fields": [
      "reference_surface_family",
      "reference_instance_id",
      "approved_profile_id",
      "canonical_profile_designation",
      "alternate_profile_designation",
      "export_artifact_refs",
      "target_domain_coverage_by_profile",
      "source_artifact_hashes",
      "derivation_refs",
      "conformance_gating_result_by_profile"
    ],
    "implementation_target_domains": [
      "react_tree",
      "route_module",
      "state_store_contract",
      "component_binding_map",
      "css_token_map",
      "test_targets"
    ],
    "implementation_exports_must_be_canonical_artifact_derived": true,
    "side_channel_prompt_or_local_heuristic_inputs_rejected": true,
    "exported_provenance_hooks_required": true,
    "exported_implementation_bindings_required": true,
    "css_token_map_is_bounded_family_mapping_only": true,
    "rendered_law_must_survive_export": [
      "evidence_before_commit_visibility",
      "advisory_authoritative_distinction",
      "deontic_gating",
      "observable_state_feedback",
      "same_context_reachability_consumption"
    ],
    "canonical_export_conformance_requirement": "pass",
    "alternate_export_conformance_requirement": "pass",
    "compiler_exports_must_consume_frozen_v36d_conformance_report_structure": true,
    "compiler_exports_must_consume_frozen_v36d_conformance_aggregation_rule": true,
    "implementation_exports_may_not_use_unconstrained_css_theme_overrides": true,
    "no_event_stream_or_worker_prose_truth_substitution": true,
    "ui_artifacts_may_express_but_may_not_mint_authority": true
  },
  "evidence_integration_requirements": {
    "closeout_required_block_schema": "v36e_surface_compiler_export_evidence@1",
    "canonical_closeout_evidence_required": true,
    "closeout_required_block_keys": [
      "schema",
      "contract_source",
      "evidence_input_path",
      "ux_surface_compiler_export_schema_path",
      "ux_surface_compiler_export_schema_hash",
      "ux_surface_compiler_variant_manifest_schema_path",
      "ux_surface_compiler_variant_manifest_schema_hash",
      "ux_surface_compiler_export_reference_path",
      "ux_surface_compiler_export_reference_hash",
      "ux_surface_compiler_variant_manifest_reference_path",
      "ux_surface_compiler_variant_manifest_reference_hash",
      "reference_binding_tuple_equality_verified",
      "v36a_reference_pair_consumed_without_drift",
      "v36b_reference_pair_consumed_without_drift",
      "v36c_rendered_surface_consumed_without_drift",
      "v36d_diagnostics_conformance_consumed_without_drift",
      "canonical_profile_binding_verified",
      "alternate_profile_binding_verified",
      "canonical_profile_id_verified_against_v36a_table",
      "alternate_profile_id_verified_against_v36a_table",
      "approved_profile_cardinality_verified",
      "compiler_export_derivation_verified",
      "implementation_target_domains_verified",
      "canonical_profile_target_domains_verified",
      "alternate_profile_target_domains_verified",
      "side_channel_prompt_or_local_heuristic_inputs_rejected",
      "exported_provenance_hooks_verified",
      "exported_implementation_bindings_verified",
      "canonical_export_emitted_and_pass_gated",
      "alternate_lawful_export_emitted_and_pass_gated",
      "conformance_gating_for_emitted_profiles_verified",
      "out_of_table_profile_combinations_rejected",
      "unconstrained_css_override_drift_rejected",
      "no_visual_authority_inflation_preserved",
      "v35_authority_baseline_unchanged",
      "verification_passed",
      "metric_key_cardinality",
      "metric_key_exact_set_equal_v64",
      "notes"
    ]
  },
  "test_requirements": {
    "ux_surface_compiler_export_schema_serialization_deterministic": true,
    "ux_surface_compiler_variant_manifest_schema_serialization_deterministic": true,
    "reference_export_serialization_deterministic": true,
    "reference_variant_manifest_serialization_deterministic": true,
    "reference_binding_tuple_equality_verified": true,
    "v36a_reference_pair_consumed_without_drift": true,
    "v36b_reference_pair_consumed_without_drift": true,
    "v36c_rendered_surface_consumed_without_drift": true,
    "v36d_diagnostics_conformance_consumed_without_drift": true,
    "canonical_profile_binding_verified": true,
    "alternate_profile_binding_verified": true,
    "canonical_profile_id_verified_against_v36a_table": true,
    "alternate_profile_id_verified_against_v36a_table": true,
    "approved_profile_cardinality_verified": true,
    "compiler_export_derivation_verified": true,
    "implementation_target_domains_verified": true,
    "canonical_profile_target_domains_verified": true,
    "alternate_profile_target_domains_verified": true,
    "side_channel_prompt_or_local_heuristic_inputs_rejected": true,
    "exported_provenance_hooks_verified": true,
    "exported_implementation_bindings_verified": true,
    "canonical_export_emitted_and_pass_gated": true,
    "alternate_lawful_export_emitted_and_pass_gated": true,
    "conformance_gating_for_emitted_profiles_verified": true,
    "out_of_table_profile_combinations_rejected": true,
    "unconstrained_css_override_drift_rejected": true,
    "no_visual_authority_inflation_preserved": true,
    "v35_authority_baseline_unchanged": true
  }
}
```

Interpretive notes:

- v65 defines compiler-export artifacts only; it does not yet authorize broad route-family
  realization, repo-wide replacement of hand-authored surfaces, or runtime self-mutation.
- emitted compiler exports must remain implementation-facing canonical contracts rather
  than prompt-side design suggestions.
- `css_token_map` in this arc is a bounded family-local implementation mapping only; it
  does not authorize a generalized token system, theme program, or palette expansion.
- lawful variation in v65 is bounded to the frozen first-family two-profile table; this
  arc is not a general variant search program.

## E1) Surface Compiler Export Baseline (`V36-E`)

### Goal

Make `V36-E` real as a deterministic surface-compiler export substrate rather than manual
variant coding.

### Scope

- add canonical `ux_surface_compiler_export@1` and canonical
  `ux_surface_compiler_variant_manifest@1` schemas for the bounded
  `artifact_inspector_advisory_workbench` family;
- add one accepted deterministic canonical-profile compiler export and one accepted
  deterministic alternate lawful export, bound by the shared
  `reference_surface_family`, `reference_instance_id`, and `approved_profile_id` fields
  back to the released `V36-A`, `V36-B`, `V36-C`, and `V36-D` substrate;
- require the alternate lawful export to receive its own deterministic diagnostics and
  conformance evaluation under the frozen `V36-D` report structure and aggregation rule
  before it can be emitted as lawful;
- freeze exact compiler export coverage for the implementation target domains listed in
  the contract:
  React tree, route module, state-store contract, component-binding map, CSS-token map,
  and test targets;
- freeze exact two-profile release shape:
  one `artifact_inspector_reference` export plus one `artifact_inspector_alternate`
  export, with all out-of-table profile combinations rejected;
- freeze minimum required structure for the new capstone artifacts:
  `ux_surface_compiler_export@1` and `ux_surface_compiler_variant_manifest@1`;
- require emitted exports to preserve the frozen rendered-law invariants and to remain
  gated by consumed diagnostics/conformance rather than local compiler heuristics.

### Acceptance

- for one bounded ADEU-native workbench family, the repo can emit one canonical compiler
  export plus one explicitly approved alternate lawful export from typed UX artifacts
  without deontic, trust-boundary, or authority drift, with both profiles independently
  pass-gated by the frozen `V36-D` conformance rule;
- the emitted export pair is coherently bound back to the released accepted `V36-A`,
  `V36-B`, `V36-C`, and `V36-D` substrate and the frozen two-profile table.

### Out of Scope

- broad compiler rollout across unrelated route families;
- more than two approved export profiles;
- profile-table or morph-axis widening;
- runtime application of the exports without explicit future lock text.

## E2) Surface Compiler Export Evidence + Determinism/Guard Suite (`V36-E`)

### Goal

Make the v65 `V36-E` release closeout-grade rather than relying on schema files and one
happy export pair alone.

### Scope

- materialize canonical `v36e_surface_compiler_export_evidence@1`;
- validate schema/reference outputs against the frozen `V36-E` contract and consumed
  `V36-A` / `V36-B` / `V36-C` / `V36-D` substrate;
- prove exact two-profile emission, exact approved-profile-table consumption, and
  fail-closed rejection of out-of-table profile combinations;
- prove exported provenance hooks, implementation bindings, implementation target domains,
  and diagnostics/conformance gating remain deterministic on a per-profile basis;
- prove compiler outputs do not mint authority, do not substitute event/prose truth, and
  do not rely on unconstrained CSS/theme overrides to weaken required salience or
  evidence visibility;
- preserve stop-gate continuity against v64 with no schema-family or metric-key drift.

### Acceptance

- v65 closeout can prove that the `V36-E` compiler-export layer is canonical,
  deterministic, bound to the released accepted `V36-A` / `V36-B` / `V36-C` /
  `V36-D` substrate, preserves the frozen two-profile lawful-variant range, and
  rejects out-of-table combinations fail closed, with both emitted profiles
  independently pass-gated under the frozen `V36-D` conformance rule;
- no stop-gate schema-family or metric-key drift is introduced by the compiler-export
  lane.

### Out of Scope

- compiler export for any route family beyond the bounded artifact inspector workbench;
- automatic runtime mutation or route replacement from export output;
- broad lawful-variant exploration beyond the frozen canonical and alternate profiles.

## Exit Criteria

1. `E1` and `E2` merge with green CI.
2. `ux_surface_compiler_export@1` and `ux_surface_compiler_variant_manifest@1` exist with
   deterministic accepted reference artifacts on `main`.
3. Exactly two approved emitted profiles exist:
   `artifact_inspector_reference` and `artifact_inspector_alternate`.
4. Export outputs remain coherently bound to the released accepted `V36-A`, `V36-B`,
   `V36-C`, and `V36-D` substrate and preserve frozen authority boundaries.
5. Both emitted profiles are independently pass-gated under the frozen `V36-D`
   conformance-report structure and aggregation rule.
6. Out-of-table profile combinations fail closed.
7. The canonical evidence block `v36e_surface_compiler_export_evidence@1` is emitted and
   records `metric_key_exact_set_equal_v64 = true`.
8. No runtime auto-repair, broad route-family compiler rollout, or repo-wide design-system
   widening is released in the arc.

## Why This Arc, Not `O1` / `O2` / `O3`

- compiler export and lawful variants should not ship before deterministic diagnostics and
  typed conformance exist over the bounded rendered reference surface;
- `V36-D` is now closed, so the next safe move in the family is the bounded export lane
  the planning doc already sequenced after diagnostics;
- the closeout-hardening bundle remains operational and orthogonal; it does not replace
  the missing `V36-E` compiler/export substrate.

## Recommendation

- lock `vNext+65` as a narrow `V36-E` surface-compiler export baseline only;
- require one canonical export plus one alternate lawful export over the bounded first
  family, with both exports independently pass-gated under the frozen `V36-D`
  conformance rule, not a broad variant program;
- defer any further widening until this exact two-profile compiler/export lane is
  canonical, evidence-backed, and closed.
