# Locked Recursive Coordinate Adoption v0

Status: additive-only lock for bounded adoption of the recursive coordinate core bundle.

This lock consumes:

- `docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md`
- `docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md`
- `docs/DRAFT_RECURSIVE_COORDINATE_SUPPORT_APPENDICES_v0.md`

The support appendices remain coexisting non-override companions.
This lock adopts only the bounded core bundle and the bounded migration/lint posture for
current repo use.
It does not silently supersede the earlier standalone support drafts by existence alone.
It adopts the five core primitives and the explicitly listed bounded current-repo rules
in this document, not every explanatory sentence in the consumed narrative wrappers.

## 1. Direct Lock

The repo adopts the following five primitives as the current recursive coordinate control-
plane bundle for bounded use:

1. `recursive_coordinate_system@1`
2. `lawful_cell_occupancy@1`
3. `coordinate_transition_rule@1`
4. `institutional_force_profile@1`
5. `recursive_schema_coordinate@1`

The bounded rule set adopted with those primitives is:

- released repo operative surfaces are currently instance-bound

The bounded reserved-cell posture adopted with those primitives is:

- `meta × operative` remains representable but not currently lawful

## 2. Bounded Adoption Surface

This lock authorizes the core bundle for:

- schema authoring guidance
- schema review and placement analysis
- warning-only coordinate lint design and emission
- curated coordinate annotation on candidate or newly reviewed artifacts
- migration crosswalk use for interpretation of overloaded legacy vocabulary

This lock does not authorize:

- hard release blocking by coordinate noncompliance
- mandatory coordinate records on every released artifact family
- reserved-cell activation
- automatic force promotion
- retroactive forced migration of released legacy posture fields
- silent supersession of existing lock docs or released contracts

## 3. Adoption Boundary Rows

### Allowed Now

- `reference_recursive_coordinate_core_bundle`
- `emit_warning_only_coordinate_annotation`
- `emit_warning_only_coordinate_lint`
- `record_non_release_coordinate_review_hold`
- `attach_traceable_coordinate_binding`
- `use_crosswalk_for_legacy_field_interpretation`

For this lock, a coordinate review hold is an internal review outcome only.
It may pause or reject a local review conclusion, but it is not a CI or release gate.

### Allowed With Later Lock

- `treat_occupancy_violation_as_release_blocking`
- `require_coordinate_record_for_released_family`
- `activate_reserved_cell`
- `replace_legacy_posture_fields_repo_wide`
- `treat_force_promotion_witness_absence_as_release_fail`

### Forbidden Now

- `treat_support_appendix_as_self_executing_lock`
- `claim_meta_operative_is_lawful_now`
- `auto_promote_force_band_without_witness`
- `silently_supersede_existing_lock_authority`

## 4. Support Companion Relation

The following remain support-layer companions and do not become lock-level gates by this
document:

- `docs/support/ADEU_SCHEMA_META_GRAMMAR.md`
- `docs/support/AGENTIC_DE_TYPE_GRAMMAR.md`
- `docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE.md`
- `docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md`
- `docs/support/Recursive Schema Coordinate Space.md`
- `docs/support/Recursive Schema Coordinate Space hardening pass.md`
- `docs/support/RECURSIVE_COORDINATE_SYSTEM_PROMOTION_READY.md`
- `docs/DRAFT_RECURSIVE_COORDINATE_SUPPORT_APPENDICES_v0.md`

They remain legitimate interpretive or migration support surfaces.
They are not, by themselves, implementation-authoritative release gates.

## 5. Acceptance

This bounded adoption is complete when:

1. the five-primitives core bundle is the preferred repo reference for recursive
   coordinate review;
2. current use is warning-only and explicitly non-release-blocking;
3. support appendices remain explicitly non-overriding;
4. any later widening into release gates, reserved-cell activation, or mandatory legacy
   migration requires a later lock or released contract;
5. the current operative placement rule remains typed as repo-constitutional posture,
   not universal ADEU law.

## 6. Machine-Checkable Lock Summary

```json
{
  "schema": "recursive_coordinate_adoption_lock@1",
  "lock_id": "lock:recursive_coordinate_adoption_v0",
  "consumed_refs": [
    "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_SUPPORT_APPENDICES_v0.md"
  ],
  "adopted_core_primitives": [
    "recursive_coordinate_system@1",
    "lawful_cell_occupancy@1",
    "coordinate_transition_rule@1",
    "institutional_force_profile@1",
    "recursive_schema_coordinate@1"
  ],
  "adopted_bounded_current_repo_rules": [
    "released_repo_operative_surfaces_are_currently_instance_bound"
  ],
  "retained_current_repo_constitutional_rules": [
    "released_repo_operative_surfaces_are_currently_instance_bound"
  ],
  "retained_reserved_cell_postures": [
    "meta:operative_reserved_not_currently_lawful"
  ],
  "allowed_now_actions": [
    "reference_recursive_coordinate_core_bundle",
    "emit_warning_only_coordinate_annotation",
    "emit_warning_only_coordinate_lint",
    "record_non_release_coordinate_review_hold",
    "attach_traceable_coordinate_binding",
    "use_crosswalk_for_legacy_field_interpretation"
  ],
  "later_lock_required_actions": [
    "treat_occupancy_violation_as_release_blocking",
    "require_coordinate_record_for_released_family",
    "activate_reserved_cell",
    "replace_legacy_posture_fields_repo_wide",
    "treat_force_promotion_witness_absence_as_release_fail"
  ],
  "forbidden_actions": [
    "treat_support_appendix_as_self_executing_lock",
    "claim_meta_operative_is_lawful_now",
    "auto_promote_force_band_without_witness",
    "silently_supersede_existing_lock_authority"
  ],
  "support_companion_relation": {
    "current_markdown_authority_relation": "coexisting_non_override",
    "requires_later_lock_for_supersession": true
  }
}
```
