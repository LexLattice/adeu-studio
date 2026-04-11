# Draft Recursive Coordinate Support Appendices v0

Status: support-layer appendix index and companion for the recursive coordinate doctrine
bundle.

Authority posture:

- authority layer: `support`
- current markdown authority relation: `coexisting_non_override`
- requires later lock for supersession: yes

This document does not add new coordinate law.

Its purpose is to classify which current markdown sources remain companion analysis,
historical hardening lineage, or support migration material once the core bundle is
extracted into a separate doctrine surface.

Current treatment of the earlier recursive-coordinate drafts:

- they remain committed standalone support docs
- they are indexed here as appendices
- they are not implicitly superseded or folded into the core bundle by existence alone

## 1. Direct Answer

The recursive coordinate lineage now splits into:

- one governing-candidate core bundle
- several support appendices that remain useful but non-gating

This document records that split explicitly so later readers do not mistake historical
analysis or migration aids for the control-plane core.

## 2. Support Appendix Rows

| source_ref | current role | current authority relation | why not core |
| --- | --- | --- | --- |
| `docs/support/ADEU_SCHEMA_META_GRAMMAR.md` | higher-order schema-authoring analysis | `coexisting_non_override` | broader than the coordinate bundle; informs it but is not itself the coordinate control plane |
| `docs/support/AGENTIC_DE_TYPE_GRAMMAR.md` | lower-order project-type exemplar | `coexisting_non_override` | concrete descendant grammar, not a repo-wide coordinate primitive |
| `docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE.md` | early governance-axis theory note | `coexisting_non_override` | superseded by later hardened governance treatment |
| `docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md` | hardened governance-axis companion doctrine | `coexisting_non_override` | strong companion doctrine, but not part of the five coordinate primitives |
| `docs/support/Recursive Schema Coordinate Space.md` | initial geometry exploration | `coexisting_non_override` | historical geometry analysis, not the promoted bundle |
| `docs/support/Recursive Schema Coordinate Space hardening pass.md` | repo-grounded hardening analysis | `coexisting_non_override` | hardening lineage and evidence base, not the final core surface |
| `docs/support/RECURSIVE_COORDINATE_SYSTEM_PROMOTION_READY.md` | promotion and claim-typing analysis | `coexisting_non_override` | readiness and adoption analysis, not a long-term control-plane primitive |

## 3. Intended Support Roles

Support appendices remain legitimate for:

- tracing how the geometry was selected and hardened
- justifying claim typing and reserved-cell posture
- interpreting legacy vocabulary during migration
- supporting review and analysis
- seeding later released schemas and lints

Support appendices should not be used by themselves as:

- hard release gates
- implicit supersession of existing lock docs
- direct authority to activate reserved cells
- self-executing migration mandates

## 4. Preferred Reading Order

For the current bundle:

1. `docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md`
2. `docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md`
3. `docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md`
4. support appendix sources listed above as needed

That order keeps the control-plane core ahead of the historical and analytic lineage.

## 5. Machine-Checkable Appendix Index

```json
{
  "schema": "recursive_coordinate_support_appendix_index@1",
  "artifact": "docs/DRAFT_RECURSIVE_COORDINATE_SUPPORT_APPENDICES_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support",
  "current_markdown_authority_relation": "coexisting_non_override",
  "requires_later_lock_for_supersession": true,
  "appendix_rows": [
    {
      "source_ref": "docs/support/ADEU_SCHEMA_META_GRAMMAR.md",
      "role": "higher_order_meta_schema_analysis",
      "control_plane_status": "support_only"
    },
    {
      "source_ref": "docs/support/AGENTIC_DE_TYPE_GRAMMAR.md",
      "role": "lower_order_project_type_exemplar",
      "control_plane_status": "support_only"
    },
    {
      "source_ref": "docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE.md",
      "role": "historical_governance_axis_draft",
      "control_plane_status": "support_only"
    },
    {
      "source_ref": "docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md",
      "role": "hardened_governance_axis_companion",
      "control_plane_status": "support_only"
    },
    {
      "source_ref": "docs/support/Recursive Schema Coordinate Space.md",
      "role": "historical_geometry_exploration",
      "control_plane_status": "support_only"
    },
    {
      "source_ref": "docs/support/Recursive Schema Coordinate Space hardening pass.md",
      "role": "repo_grounding_and_hardening_lineage",
      "control_plane_status": "support_only"
    },
    {
      "source_ref": "docs/support/RECURSIVE_COORDINATE_SYSTEM_PROMOTION_READY.md",
      "role": "promotion_readiness_analysis",
      "control_plane_status": "support_only"
    }
  ],
  "preferred_control_plane_refs": [
    "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
    "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md"
  ]
}
```
