# Draft Recursive Coordinate Core Bundle v0

Status: planning-layer architecture/decomposition doctrine candidate for bounded
repo-wide schema-artifact placement and transition review.

Authority posture:

- authority layer: `planning`
- authority surface kind: `architecture_decomposition`
- current doctrinal force under repo authority layering: planning-layer interpretive
  doctrine
- intended promotion target: governing candidate core
- implementation authority transferred: no
- current markdown authority relation: `coexisting_non_override`
- requires later lock for supersession: yes

Per `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`, this planning/decomposition
surface is authoritative for conceptual structure and interpretive boundaries only until
a later lock doc or released contract binds it more strongly.

This document is not a lock doc.

It does not by itself authorize:

- release-blocking coordinate gates
- retroactive forced reclassification of released artifacts
- reserved-cell activation
- automatic force promotion
- repo-wide mandatory migration of legacy posture vocabularies

Related support inputs:

- `docs/support/Recursive Schema Coordinate Space.md`
- `docs/support/Recursive Schema Coordinate Space hardening pass.md`
- `docs/support/RECURSIVE_COORDINATE_SYSTEM_PROMOTION_READY.md`
- `docs/support/ADEU_SCHEMA_META_GRAMMAR.md`
- `docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md`
- `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md`

## 1. Direct Answer

The retained recursive coordinate geometry is promoted here as one bounded core bundle.

The intended governing-candidate core consists of five primitives only:

1. `recursive_coordinate_system@1`
2. `lawful_cell_occupancy@1`
3. `coordinate_transition_rule@1`
4. `institutional_force_profile@1`
5. `recursive_schema_coordinate@1`

Everything else in the current support lineage remains companion analysis, migration
support, or audit/reporting support.

## 2. Core Coordinate System

The retained base grid is:

`binding_depth × institutional_force`

with exactly four levels on each axis.

Binding depth:

1. `meta`
2. `family`
3. `bounded`
4. `instance`

Institutional force:

1. `observational`
2. `interpretive`
3. `governing`
4. `operative`

These remain the only primary recursive axes in the current doctrine candidate.

The following remain non-axis structures:

- ODEU: mandatory local node structure
- lifecycle/status: overlay
- visibility/posture: overlay
- trust state: overlay
- phase boundary: overlay
- carrier and lineage: compatibility and taxonomy layers, not coordinates
- derivation/projection/promotion: witness-bearing edge relations, not coordinates

Coordinates attach to semantic artifact role rather than storage format.

Required auxiliary control fields for placed artifacts:

- `placement_basis`
- `coverage_scope` when a meta-level observational or interpretive surface ranges
  downward
- `carrier`
- `force_profile`
- `overlays`
- `derivation_witness_refs`

## 3. Lawful Cell Occupancy

The retained occupancy matrix is:

| binding_depth \ institutional_force | observational | interpretive | governing | operative |
| ----------------------------------- | ------------: | -----------: | --------: | --------: |
| `meta`                              | `lawful_core` | `lawful_core` | `lawful_core` | `reserved` |
| `family`                            | `lawful_core` | `lawful_core` | `lawful_core` | `invalid` |
| `bounded`                           | `lawful_core` | `lawful_core` | `lawful_core` | `invalid` |
| `instance`                          | `lawful_core` | `lawful_rare` | `lawful_core` | `lawful_core` |

Status meanings:

- `lawful_core`: normal released use
- `lawful_rare`: valid but requires explicit justification
- `invalid`: conceptually wrong under the retained doctrine
- `reserved`: representable in the abstract grid but not currently lawful in this repo

Current repo constitutional rules carried by this bundle:

- meta observational or interpretive surfaces that range downward over lower-depth
  objects must declare `coverage_scope`
- released repo operative surfaces are currently instance-bound
- lawful-rare placements require explicit review justification

## 4. Institutional Force Profile

Every placed artifact must resolve to exactly one dominant force band:

- `observational`
- `interpretive`
- `governing`
- `operative`

Support qualifiers may refine but never replace the dominant band.

Allowed support qualifiers in the current doctrine candidate:

- `evidentiary`
- `interpretation_support`
- `gating`
- `execution_binding`

Current repo hygiene cap:

- maximum two support qualifiers per artifact before the surface should be split

This cap is a current repo implementation discipline, not a timeless ADEU axiom.

## 5. Coordinate Transition Rule

The retained transition law is:

- specialization or binding may narrow depth but may not mint new force
- observational to interpretive requires a new interpretive artifact, not relabeling
- interpretive to governing requires explicit ratification, released contract, lock
  binding, or deterministic adjudication
- observational to governing requires a separate normative surface and explicit
  promotion witness
- under the current repo constitutional posture, governing-to-operative placement in
  released repo surfaces additionally requires concrete activation or materialization
  witness at `instance` depth only
- overlay changes do not relocate the coordinate unless they hide an actual force or
  depth change

The constitutive anti-laundering rule remains:

- projection may express but may not mint authority

## 6. Recursive Schema Coordinate Record

Every concrete placement record should bind at least:

- `placement_subject_ref`
- `placement_basis`
- `coordinate.binding_depth`
- `coordinate.institutional_force`
- `force_profile`
- `coverage_scope` when required
- `carrier`
- `overlays`
- `derivation_witness_refs`
- `placement_confidence`

This record shape is the intended repo-native placement contract for future emitted
coordinate annotations.

## 7. Support Appendices Are Out Of Core

The following remain support companions rather than core control-plane primitives:

- coordinate vocabulary crosswalk material
- narrative placement report material
- promotion-readiness report material
- earlier geometry and hardening lineage notes
- vertical-alignment companion doctrine
- higher-order meta-schema analysis
- lower-order project-type exemplars

See:

- `docs/DRAFT_RECURSIVE_COORDINATE_SUPPORT_APPENDICES_v0.md`

Those materials remain useful and active for interpretation.
They are not themselves the promoted core bundle.

## 8. Current Allowed Uses

This core bundle may already be used for:

- schema authoring guidance
- coordinate placement review
- warning-only lint design
- curated coordinate annotations on candidate artifacts
- vocabulary drift analysis using the support crosswalk

Hard release gating still requires a later lock or released contract that binds the
bundle explicitly.

## 9. Machine-Checkable Seed Summary

```json
{
  "schema": "recursive_coordinate_core_bundle_seed@1",
  "artifact": "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
  "artifact_status": "draft",
  "authority_layer": "planning",
  "authority_surface_kind": "architecture_decomposition",
  "current_doctrinal_force": "planning_layer_interpretive_doctrine",
  "implementation_authority_transferred": false,
  "current_markdown_authority_relation": "coexisting_non_override",
  "requires_later_lock_for_supersession": true,
  "core_primitives": [
    "recursive_coordinate_system@1",
    "lawful_cell_occupancy@1",
    "coordinate_transition_rule@1",
    "institutional_force_profile@1",
    "recursive_schema_coordinate@1"
  ],
  "current_repo_constitutional_rules": [
    "meta_downward_surfaces_require_coverage_scope",
    "released_repo_operative_surfaces_are_currently_instance_bound",
    "lawful_rare_cells_require_explicit_justification"
  ],
  "allowed_now": [
    "schema_authoring_guidance",
    "coordinate_review",
    "warning_only_lint_design",
    "curated_coordinate_annotations"
  ],
  "requires_later_lock": [
    "release_blocking_coordinate_gates",
    "mandatory_coordinate_records_for_released_families",
    "reserved_cell_activation",
    "automatic_force_promotion",
    "repo_wide_legacy_vocabulary_migration"
  ]
}
```
