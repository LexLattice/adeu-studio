# LOCKED_CONTINUATION_vNEXT_PLUS183

## Status

Bounded follow-on lock draft for `V66-B` (step-2 migration binding / reader
projection).

This file remains a starter lock draft until the associated starter-bundle gate is
accepted and the bundle is intentionally committed as the operative `V66-B`
implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `V66`
- slice: `V66-B`
- branch-local execution target: `arc/v66-r2`

## Purpose

Freeze the bounded ANM-native migration / reader-projection posture for `V66-B`
so the repo can add one typed migration-binding seam, one typed generated
reader-projection manifest, and one typed semantic diff report over the already
shipped `V66-A` source-set / authority-profile / class-policy basis without
reopening `V47` language / IR / checker ownership, silently superseding current
markdown authority, minting generated-reader authority, minting semantic-diff
authority, or flattening lock / architecture / planning / support / non-governance
docs into one migration class by default.

`vNext+183` authorizes docs plus the first `V66-B` implementation path over
existing repo-owned packages, but not ANM language widening, selector or
predicate ownership widening, policy-consumer widening, stable compile-report
artifacts, prose-boundary notice artifacts, repo-wide `.adeu.md` rename posture,
implicit markdown supersession, generated-reader authority, semantic-diff
authority, runtime authority minting, advisory-to-live promotion, or
hidden-cognition governance.

In `vNext+183`, the new `V66-B` outputs are documentation-governance migration
and review surfaces only. They do not change current runtime behavior, current
markdown authority, released `V47` ANM source semantics, shipped `V66-A`
classification semantics, or generated-reader authority posture by default.

## Instantiated Here

- `V66-B` instantiates only one bounded migration / reader-projection seam:
  - existing repo-owned packages:
    - `adeu_semantic_source`
    - `adeu_commitments_ir`
    - `adeu_semantic_compiler`
  - one consumed shipped `V66-A` basis only:
    - shipped `anm_source_set_manifest@1`
    - shipped `anm_doc_authority_profile@1`
    - shipped `anm_doc_class_policy@1`
  - the same governed source set only:
    - one shipped governed ANM source set only
    - no fresh source-set widening by default
  - one new bounded migration / reader artifact set only:
    - `anm_migration_binding_profile@1`
    - `anm_reader_projection_manifest@1`
    - `anm_semantic_diff_report@1`
  - one explicit migration posture only:
    - registered host / companion relation remains explicit
    - supersession remains transition-law-gated
    - companion proximity is not supersession by itself
  - one explicit reader-projection posture only:
    - generated reader projection remains non-authoritative
    - stale or missing projection remains visible and fail-closed
  - one explicit semantic-diff posture only:
    - semantic diff records authority-surface additions / removals / changes
    - semantic diff is not authority by itself
  - one explicit ordering law:
    - `V66-B` is downstream of shipped `V66-A`
    - it does not replace `V47` language / IR / checker / evaluator ownership
    - it does not replace current markdown authority
    - it does not replace shipped `V66-A` source-set / authority-profile /
      class-policy ownership
    - advisory adoption hardening remains deferred to `V66-C`
  - one explicit posture law:
    - migration binding remains typed and replayable
    - reader projection manifest remains typed and replayable
    - semantic diff report remains typed and replayable
    - same shipped `V66-A` basis plus same generated reader inputs plus same
      frozen policy yields the same `V66-B` outputs
    - contradictory host / companion migration posture fails closed
    - supersession claim without explicit transition law fails closed
    - generated projection authority overread fails closed
    - semantic diff authority overread fails closed

## Required Deliverables / Exit Conditions

- one typed `anm_migration_binding_profile@1` over shipped `V66-A` basis only
- one typed `anm_reader_projection_manifest@1` over the same governed source set only
- one typed `anm_semantic_diff_report@1` over the same governed source set only
- deterministic reference fixtures and schema export for the `V66-B` surfaces
- one repo-scale migration / projection / diff entrypoint over existing package
  seams only
- tests that prove:
  - shipped `V66-A` basis remains the only accepted migration / projection basis
  - host / companion registration remains explicit and fail-closed
  - supersession claim without explicit transition law fails closed
  - generated reader views remain non-authoritative
  - semantic diff remains non-authoritative
  - same governed source set remains explicit and non-widened
  - no new `D@1` language widening lands in this slice
  - no compile-report or prose-boundary doctrine lands in this slice

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS183.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+183",
  "target_path": "V66-B",
  "slice": "V66-B",
  "family": "V66",
  "branch_local_execution_target": "arc/v66-r2",
  "target_scope": "one_bounded_anm_native_migration_and_reader_projection_slice_over_one_exact_shipped_v66a_source_set_only",
  "implementation_packages": [
    "adeu_semantic_source",
    "adeu_commitments_ir",
    "adeu_semantic_compiler"
  ],
  "api_surfaces": [],
  "cli_or_validation_entrypoints_for_v66b": [
    "anm-migration-check",
    "anm-reader-check",
    "anm-diff-check"
  ],
  "cli_entrypoints_are_repo_validation_surfaces_not_runtime_api_surfaces": true,
  "prerequisite_lock_doc": "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md",
  "prerequisite_decision_doc": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS182.md",
  "prerequisite_assessment_doc": "docs/ASSESSMENT_vNEXT_PLUS182_EDGES.md",
  "family_architecture_doc": "docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md",
  "family_support_mapping_doc": "docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66B_IMPLEMENTATION_MAPPING_v0.md",
  "admitted_shaping_inputs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v51.md",
    "docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md",
    "docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md"
  ],
  "required_prior_lane_evidence_surfaces": [
    "artifacts/agent_harness/v182/evidence_inputs/v66a_anm_native_documentation_practice_starter_evidence_v182.json"
  ],
  "consumed_record_shapes_for_v66b": [
    "anm_source_set_manifest@1",
    "anm_doc_authority_profile@1",
    "anm_doc_class_policy@1"
  ],
  "emitted_record_shapes_for_v66b": [
    "anm_migration_binding_profile@1",
    "anm_reader_projection_manifest@1",
    "anm_semantic_diff_report@1"
  ],
  "required_schema_ids_for_v66b": [
    "anm_migration_binding_profile@1",
    "anm_reader_projection_manifest@1",
    "anm_semantic_diff_report@1"
  ],
  "selected_record_shapes": [
    "anm_source_set_manifest@1",
    "anm_doc_authority_profile@1",
    "anm_doc_class_policy@1",
    "anm_migration_binding_profile@1",
    "anm_reader_projection_manifest@1",
    "anm_semantic_diff_report@1"
  ],
  "selected_consumed_v66a_lineage_for_v66b": "shipped_v66a_source_set_authority_profile_class_policy_only",
  "v66b_outputs_must_reference_exact_consumed_v66a_basis": true,
  "consumed_v66a_basis_requires_ref_and_hash": true,
  "v66b_does_not_reemit_or_mutate_v66a_source_set_by_default": true,
  "same_governed_source_set_only_for_v66b": true,
  "fresh_source_set_widening_selected_for_v66b": false,
  "selected_migration_binding_surface_for_v66b": true,
  "selected_reader_projection_surface_for_v66b": true,
  "selected_semantic_diff_surface_for_v66b": true,
  "selected_compile_report_surface_for_v66b": false,
  "selected_prose_boundary_notice_surface_for_v66b": false,
  "selected_markdown_supersession_without_explicit_transition_law_for_v66b": false,
  "selected_generated_reader_authority_for_v66b": false,
  "selected_semantic_diff_authority_for_v66b": false,
  "selected_v47_language_widening_for_v66b": false,
  "migration_binding_profile_is_row_shaped_for_v66b": true,
  "reader_projection_manifest_is_row_shaped_for_v66b": true,
  "semantic_diff_report_is_row_shaped_for_v66b": true,
  "anm_migration_binding_profile_shape_for_v66b": {
    "top_level": [
      "schema_id",
      "migration_binding_profile_id",
      "consumed_source_set_manifest_ref",
      "consumed_source_set_manifest_hash",
      "consumed_doc_class_policy_ref",
      "consumed_doc_class_policy_hash",
      "consumed_authority_profile_set_ref_or_hash",
      "binding_rows"
    ],
    "binding_row": [
      "binding_id",
      "host_doc_ref",
      "companion_doc_ref",
      "host_profile_ref",
      "companion_profile_ref_or_none",
      "binding_posture",
      "current_markdown_authority_relation",
      "supersession_claim_status",
      "explicit_transition_law_ref_or_none",
      "generated_reader_projection_refs_or_none",
      "semantic_diff_ref_or_none"
    ]
  },
  "anm_reader_projection_manifest_shape_for_v66b": {
    "top_level": [
      "schema_id",
      "projection_manifest_id",
      "consumed_source_set_manifest_ref",
      "consumed_source_set_manifest_hash",
      "consumed_doc_class_policy_ref",
      "consumed_doc_class_policy_hash",
      "consumed_authority_profile_set_ref_or_hash",
      "projection_rows"
    ],
    "projection_row": [
      "projection_doc_ref",
      "source_doc_ref",
      "source_profile_ref",
      "projection_required",
      "projection_requirement_source",
      "projection_status",
      "projection_authority_posture",
      "source_content_hash",
      "projection_content_hash_or_none",
      "drift_status"
    ]
  },
  "anm_semantic_diff_report_shape_for_v66b": {
    "top_level": [
      "schema_id",
      "diff_report_id",
      "consumed_source_set_manifest_ref",
      "consumed_source_set_manifest_hash",
      "consumed_doc_class_policy_ref",
      "consumed_doc_class_policy_hash",
      "consumed_authority_profile_set_ref_or_hash",
      "baseline_kind",
      "baseline_artifact_ref_or_none",
      "baseline_artifact_hash_or_none",
      "current_artifact_ref",
      "current_artifact_hash",
      "change_rows"
    ],
    "change_row": [
      "source_doc_ref",
      "baseline_profile_ref_or_none",
      "current_profile_ref",
      "change_kind",
      "surface_kind",
      "path_or_axis",
      "baseline_value_or_none",
      "current_value_or_none",
      "authority_effect_kind",
      "authority_effect_summary_or_none"
    ]
  },
  "binding_posture_values_for_v66b": [
    "registered_non_overriding_companion",
    "standalone_no_companion",
    "invalid_or_contradictory"
  ],
  "current_markdown_authority_relation_values_for_v66b": [
    "current_markdown_controlling",
    "anm_standalone_source_of_truth",
    "generated_projection_non_authoritative",
    "not_applicable"
  ],
  "supersession_claim_status_values_for_v66b": [
    "none",
    "claimed_with_explicit_transition_law",
    "claimed_without_transition_law_rejected"
  ],
  "projection_status_values_for_v66b": [
    "current",
    "stale",
    "missing",
    "not_required",
    "invalid"
  ],
  "projection_authority_posture_values_for_v66b": [
    "non_authoritative_generated_view",
    "invalid_claims_authority"
  ],
  "drift_status_values_for_v66b": [
    "in_sync",
    "source_changed_projection_stale",
    "projection_missing",
    "hash_unavailable",
    "not_required"
  ],
  "projection_requirement_source_values_for_v66b": [
    "doc_authority_profile",
    "doc_class_policy",
    "explicit_projection_manifest",
    "not_required"
  ],
  "change_kind_values_for_v66b": [
    "added",
    "removed",
    "changed",
    "unchanged",
    "initial"
  ],
  "surface_kind_values_for_v66b": [
    "source_set_entry",
    "doc_authority_profile",
    "doc_class_policy",
    "migration_binding",
    "reader_projection_manifest"
  ],
  "authority_effect_kind_values_for_v66b": [
    "review_visibility_only",
    "no_authority_minted",
    "invalid_authority_claim_rejected"
  ],
  "semantic_diff_baseline_must_be_explicit_for_v66b": true,
  "implicit_git_diff_is_not_semantic_diff_baseline_for_v66b": true,
  "semantic_diff_scope_for_v66b": [
    "source_set_entry",
    "doc_authority_profile",
    "doc_class_policy",
    "migration_binding",
    "reader_projection_manifest"
  ],
  "semantic_diff_does_not_reinterpret_d1_or_prose_for_v66b": true,
  "generated_projection_source_posture_for_v66b": "generated_projection",
  "generated_projection_may_not_be_governed_authority_source_by_itself": true,
  "generated_projection_may_not_claim_source_authority_for_v66b": true,
  "generated_projection_authority_banner_required_for_v66b": true,
  "projection_missing_or_stale_fails_only_when_projection_required_for_v66b": true,
  "transition_law_ref_must_resolve_to_lock_authority_for_v66b": true,
  "transition_law_ref_must_match_host_and_companion_for_v66b": true,
  "unresolved_transition_law_ref_fails_closed_for_v66b": true,
  "migration_binding_must_be_typed_and_replayable": true,
  "reader_projection_manifest_must_be_typed_and_replayable": true,
  "semantic_diff_report_must_be_typed_and_replayable": true,
  "same_shipped_v66a_basis_plus_same_generated_reader_inputs_plus_same_explicit_diff_baseline_plus_same_frozen_policy_yields_same_v66b_outputs": true,
  "supersession_claim_without_explicit_transition_law_fails_closed_for_v66b": true,
  "generated_reader_view_is_not_authority_by_itself_for_v66b": true,
  "semantic_diff_is_not_authority_by_itself_for_v66b": true,
  "v66b_cli_diagnostics_remain_ephemeral_without_anm_compile_report_at_1": true,
  "governs_hidden_cognition": false
}
```
