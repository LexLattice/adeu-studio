# Draft Repo Entity Role Taxonomy v0

Status: working decomposition companion for the first `V45-A` lock candidate.

Authority posture:

- this document is a planning/decomposition companion;
- it is not a lock doc;
- it does not authorize implementation or schema release by itself;
- it does not settle whole-repo taxonomy doctrine by itself.

Related inputs:

- `docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md`
- `docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v28.md`

## 1. Purpose

Provide a working multi-axis taxonomy for the bounded `repo_entity_catalog@1` surface in
the first `V45-A` slice.

## 2. Direct Answer

Repo entity classification should not collapse:

- carrier kind;
- semantic role;
- governance posture;
- derivation posture;
- mutation posture;

into one mixed label.

The first `V45-A` entity catalog should carry those axes separately.

## 3. Candidate Entity Taxonomy Axes

### 3.1 Surface kind

Illustrative surface kinds:

- doc
- schema
- code_module
- test
- fixture
- generated_artifact
- app_surface
- policy_surface
- build_or_execution_infrastructure

### 3.2 Semantic role

Illustrative semantic roles:

- semantic_authority
- implementation
- evidence
- diagnostic
- explainer
- planning
- decomposition
- support
- fixture_definition
- generated_view

### 3.3 Governance posture

Illustrative governance postures:

- draft
- advisory
- released
- locked
- superseded

### 3.4 Derivation posture

Illustrative derivation postures:

- source
- generated
- compiled
- summarized
- extracted

### 3.5 Mutation posture

Illustrative mutation postures:

- editable
- generated_only
- release_gated
- frozen

## 4. Determination Doctrine

Entity classification should use explicit support from:

1. observed repo location and file type;
2. explicit file self-description when present;
3. governing references and linked authority surfaces;
4. naming or path heuristics only as lower-precedence support.

The entity catalog should also carry whether a classification is:

- observed
- derived deterministically
- inferred heuristically
- adjudicated
- settled

## 5. `V45-A` Bounded Scope

The first `V45-A` entity taxonomy should remain bounded to schema-visible and
schema-adjacent surfaces first.

That means it should at least classify:

- authoritative package schemas;
- mirrored exported schemas;
- schema-export code surfaces;
- schema-registry companion docs;
- bounded reconstruction appendix inputs.

It should not claim whole-repo exhaustive entity classification in the first slice.

## 6. Machine-Checkable Seed Summary

```json
{
  "schema": "repo_entity_role_taxonomy_seed@1",
  "artifact": "docs/DRAFT_REPO_ENTITY_ROLE_TAXONOMY_v0.md",
  "artifact_status": "draft",
  "authority_layer": "planning_decomposition_companion",
  "target_family": "V45-A_repo_entity_catalog_lane",
  "multi_axis_taxonomy_required": true,
  "surface_kind_axis_required": true,
  "semantic_role_axis_required": true,
  "governance_posture_axis_required": true,
  "derivation_posture_axis_required": true,
  "mutation_posture_axis_required": true,
  "schema_visible_scope_first_required": true,
  "whole_repo_exhaustive_coverage_initially_deferred": true,
  "source_docs": [
    "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
    "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
  ]
}
```
