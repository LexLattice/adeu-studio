# Draft Recursive Coordinate Migration Lint Posture v0

Status: support/planning companion for bounded migration and warning-only lint rollout.

Authority posture:

- authority layer: `support`
- purpose: migration support plus non-blocking lint posture
- current markdown authority relation: `coexisting_non_override`
- requires later lock for supersession: yes
- implementation-authoritative release gating: no

This document does not define new coordinate geometry.

It defines how the adopted recursive coordinate core bundle may be introduced without
silently turning draft doctrine into hard release gates.

## 1. Direct Answer

Current posture should be:

- annotations and review use: allowed now
- coordinate lint: warning-only now
- release-blocking gates: later lock required
- repo-wide mandatory migration of overloaded legacy fields: later lock required

The current migration objective is dual:

- make the coordinate bundle usable immediately for review and analysis
- avoid accidental over-promotion into hard gating before a later lock says so

## 2. Initial Warning-Only Lint Targets

The first warning-only lint layer should focus on the bundle’s highest-signal failures:

1. missing `placement_basis`
2. missing `coverage_scope` on meta observational or interpretive surfaces that range
   downward
3. unresolved or contradictory dominant force band
4. invalid occupancy cell
5. lawful-rare occupancy without explicit justification
6. force promotion claim without explicit promotion witness
7. overloaded legacy posture fields used without coordinate crosswalk note
8. carrier-kind ambiguity that blocks carrier-coordinate compatibility review

These are review and migration warnings.
They are not release blockers under this document.

## 3. Migration Phases

### Phase 0 — Interpretation only

Allowed now:

- reference the core bundle in review
- annotate candidate artifacts manually
- use the crosswalk to interpret legacy fields

### Phase 1 — Emitted companion annotations

Allowed now:

- add optional coordinate annotations to new draft or review artifacts
- emit non-authoritative placement reports
- attach coordinate witness refs in analysis outputs

### Phase 2 — Warning-only lint

Allowed now:

- run warning-only coordinate lint in local and CI contexts
- publish warning summaries
- require explicit acknowledgment in review for lawful-rare placements

### Phase 3 — Later-lock hard gating

Later lock required:

- fail CI or release checks on invalid occupancy
- require coordinate records for released artifacts
- fail promotion when force-promotion witnesses are absent
- make carrier-coordinate compatibility mandatory

## 4. Legacy Vocabulary Migration Posture

Current legacy posture fields should be treated as follows:

- crosswalk now
- warn on overload now
- dual-emit later when control-plane shapes exist
- hard replace only after later lock or released contract

Particularly overloaded legacy fields include:

- `governance_posture`
- `derivation_posture`
- `mutation_posture`

Those should not be silently reinterpreted as canonical coordinates.

## 5. Adoption Boundary

### Allowed Now

- `emit_warning_only_coordinate_lint`
- `emit_curated_coordinate_report`
- `record_coordinate_review_note`
- `record_non_release_coordinate_review_hold`
- `attach_traceable_coordinate_binding`
- `crosswalk_legacy_posture_fields`

### Allowed With Later Lock

- `block_release_on_invalid_occupancy`
- `require_coordinate_record_for_release`
- `require_force_promotion_witness_for_release`
- `hard_fail_legacy_field_overload`
- `activate_reserved_cell`

### Forbidden Now

- `treat_warning_only_lint_as_release_gate`
- `silently_auto_reclassify_released_artifacts`
- `claim_support_companion_is_enough_for_hard_gate`

## 6. Machine-Checkable Migration Seed

```json
{
  "schema": "recursive_coordinate_migration_lint_posture@1",
  "artifact": "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support",
  "current_rollout_phase": "warning_only",
  "warning_targets": [
    "missing_placement_basis",
    "missing_required_coverage_scope",
    "unresolved_dominant_force_band",
    "invalid_occupancy_cell",
    "lawful_rare_without_justification",
    "promotion_without_witness",
    "legacy_posture_without_crosswalk",
    "carrier_coordinate_ambiguity"
  ],
  "allowed_now_actions": [
    "emit_warning_only_coordinate_lint",
    "emit_curated_coordinate_report",
    "record_coordinate_review_note",
    "record_non_release_coordinate_review_hold",
    "attach_traceable_coordinate_binding",
    "crosswalk_legacy_posture_fields"
  ],
  "later_lock_required_actions": [
    "block_release_on_invalid_occupancy",
    "require_coordinate_record_for_release",
    "require_force_promotion_witness_for_release",
    "hard_fail_legacy_field_overload",
    "activate_reserved_cell"
  ],
  "forbidden_now_actions": [
    "treat_warning_only_lint_as_release_gate",
    "silently_auto_reclassify_released_artifacts",
    "claim_support_companion_is_enough_for_hard_gate"
  ]
}
```
