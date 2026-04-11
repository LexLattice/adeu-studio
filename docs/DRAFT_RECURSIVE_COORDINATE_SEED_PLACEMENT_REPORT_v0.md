# Draft Recursive Coordinate Seed Placement Report v0

Status: support-layer curated placement report for the bounded recursive-coordinate
pilot.

Authority posture:

- authority layer: `support`
- governing refs:
  - `docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md`
  - `docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md`
  - `docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md`
- current markdown authority relation: `coexisting_non_override`
- requires later lock for supersession: yes
- release gating authorized: no

This report does not add new coordinate law.

It records one small seed set of curated placements so the recursive-coordinate bundle
can be exercised on real repo artifacts before any wider warning-only lint rollout.

## 1. Direct Answer

The first bounded pilot can be run cleanly on eight artifacts:

- three recursive-coordinate bundle docs
- two earlier schema-analysis doctrine docs
- one released meta registry schema
- one released family schema
- one materialized meta registry snapshot

The placements separate cleanly into:

- `meta × interpretive` doctrine surfaces
- `meta × governing` bounded lock adoption
- `meta × observational` registry surfaces
- `family × governing` released family contract schema

The main current gap is not geometry.
It is that several meta-level observational or interpretive surfaces still rely on
curated, external `coverage_scope` annotations rather than carrying `coverage_scope`
natively.

## 2. Pilot Scope And Method

Selection rule for this seed set:

- include both newly promoted recursive-coordinate artifacts and older supporting
  schema-doctrine artifacts
- include both markdown doctrine surfaces and released schema definitions
- include at least one materialized artifact instance
- prefer artifacts already discussed in the current coordinate lineage

Placement basis meanings used in this report:

- `doctrine_surface`
- `schema_kind_definition`
- `artifact_instance`

Snapshot basis:

- `head_commit`: `598fe70e6a2139d7a0c454c7932c98286fc6cb80`
- `working_tree_state`: `dirty_with_uncommitted_recursive_coordinate_bundle_docs`

Pilot 1 record hygiene:

- per-record `overlays` are kept narrow and carry lifecycle status only in this report
- report-context facts such as branch-local worktree state stay at report level rather
  than inside node overlays
- carrier labels below are conservative and use only clearly reusable kinds from the
  current carrier vocabulary
- `derivation_witness_refs` are used only for direct authority-binding, consumed-
  contract, or materialization witnesses
- broader interpretive ancestry is recorded under `context_refs`

## 3. Seed Placement Matrix

| artifact_ref | placement_basis | coordinate | dominant force | confidence | note |
| --- | --- | --- | --- | --- | --- |
| `docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md` | `doctrine_surface` | `meta × interpretive` | `interpretive` | `high` | meta interpretive surface; curated `coverage_scope` supplied here |
| `docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md` | `doctrine_surface` | `meta × governing` | `governing` | `high` | bounded adoption lock; no release-blocking widening authorized |
| `docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md` | `doctrine_surface` | `meta × interpretive` | `interpretive` | `high` | rollout posture only; warning-only current use |
| `docs/DRAFT_SCHEMA_META_CORE_v0.md` | `doctrine_surface` | `meta × interpretive` | `interpretive` | `high` | schema-corpus hypothesis surface; no release authority |
| `docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md` | `doctrine_surface` | `meta × interpretive` | `interpretive` | `high` | schema classification doctrine; no release authority |
| `packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json` | `schema_kind_definition` | `meta × observational` | `observational` | `high` | follows existing hardening-pass placement precedent |
| `packages/adeu_commitments_ir/schema/anm_markdown_coexistence_profile.v1.json` | `schema_kind_definition` | `family × governing` | `governing` | `medium` | released bounded family coexistence/adoption schema |
| `apps/api/fixtures/repo_description/vnext_plus99/repo_schema_family_registry_v99_reference.json` | `artifact_instance` | `meta × observational` | `observational` | `high` | concrete registry snapshot over schema rows |

## 4. Curated Coordinate Records

### 4.1 Core Bundle

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
  "placement_basis": "doctrine_surface",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "interpretive"
  },
  "force_profile": {
    "dominant_band": "interpretive",
    "support_qualifiers": []
  },
  "coverage_scope": {
    "scope_kind": "repo_schema_artifacts",
    "covered_binding_depths": ["meta", "family", "bounded", "instance"],
    "note": "The core bundle ranges downward over repo schema-artifact placement and transition review."
  },
  "carrier": {
    "carrier_superclass": "StructuralModel",
    "normalized_carrier_kinds": ["plan"]
  },
  "overlays": {
    "lifecycle_status": "draft"
  },
  "derivation_witness_refs": [],
  "context_refs": [
    "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
    "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_with_non_blocking_gap_note",
  "gap_notes": [
    "coverage_scope is explicit in this curated record but not emitted natively by the document itself"
  ]
}
```

### 4.2 Adoption Lock

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
  "placement_basis": "doctrine_surface",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "governing"
  },
  "force_profile": {
    "dominant_band": "governing",
    "support_qualifiers": ["gating"]
  },
  "carrier": {
    "carrier_superclass": "ContractGate",
    "normalized_carrier_kinds": ["contract"]
  },
  "overlays": {
    "lifecycle_status": "draft"
  },
  "derivation_witness_refs": [
    "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation"
}
```

### 4.3 Migration / Lint Posture

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md",
  "placement_basis": "doctrine_surface",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "interpretive"
  },
  "force_profile": {
    "dominant_band": "interpretive",
    "support_qualifiers": []
  },
  "coverage_scope": {
    "scope_kind": "repo_schema_artifact_rollout",
    "covered_binding_depths": ["meta", "family", "bounded", "instance"],
    "note": "The rollout posture ranges downward over how coordinate review and warning-only lint are applied."
  },
  "carrier": {
    "carrier_superclass": "StructuralModel",
    "normalized_carrier_kinds": ["plan"]
  },
  "overlays": {
    "lifecycle_status": "draft"
  },
  "derivation_witness_refs": [],
  "context_refs": [
    "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_with_non_blocking_gap_note",
  "gap_notes": [
    "coverage_scope is explicit in this curated record but not emitted natively by the document itself"
  ]
}
```

### 4.4 Schema Meta Core

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "docs/DRAFT_SCHEMA_META_CORE_v0.md",
  "placement_basis": "doctrine_surface",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "interpretive"
  },
  "force_profile": {
    "dominant_band": "interpretive",
    "support_qualifiers": []
  },
  "coverage_scope": {
    "scope_kind": "schema_corpus_hypothesis",
    "covered_binding_depths": ["meta", "family", "bounded", "instance"],
    "note": "The document reasons over the schema corpus and proposes a common envelope plus overlays abstraction."
  },
  "carrier": {
    "carrier_superclass": "StructuralModel",
    "normalized_carrier_kinds": ["plan"]
  },
  "overlays": {
    "lifecycle_status": "draft"
  },
  "derivation_witness_refs": [],
  "context_refs": [
    "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_with_non_blocking_gap_note",
  "gap_notes": [
    "coverage_scope is inferable from the document role but not carried natively"
  ]
}
```

### 4.5 Schema Role-Form Registry Doctrine

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
  "placement_basis": "doctrine_surface",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "interpretive"
  },
  "force_profile": {
    "dominant_band": "interpretive",
    "support_qualifiers": []
  },
  "coverage_scope": {
    "scope_kind": "schema_role_form_classification",
    "covered_binding_depths": ["meta", "family", "bounded", "instance"],
    "note": "The document interprets repo-wide schema classification posture for the family registry lane."
  },
  "carrier": {
    "carrier_superclass": "StructuralModel",
    "normalized_carrier_kinds": ["plan"]
  },
  "overlays": {
    "lifecycle_status": "draft"
  },
  "derivation_witness_refs": [],
  "context_refs": [
    "docs/DRAFT_SCHEMA_META_CORE_v0.md",
    "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_with_non_blocking_gap_note",
  "gap_notes": [
    "coverage_scope is inferable from the doctrine role but not carried natively"
  ]
}
```

### 4.6 Repo Schema Family Registry Schema

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json",
  "placement_basis": "schema_kind_definition",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "observational"
  },
  "force_profile": {
    "dominant_band": "observational",
    "support_qualifiers": []
  },
  "coverage_scope": {
    "scope_kind": "schema_nodes",
    "covered_binding_depths": ["meta", "family", "bounded", "instance"],
    "note": "Follows the current hardening-pass placement precedent for registry-over-schema rows."
  },
  "carrier": {
    "carrier_superclass": "CuratedSet",
    "normalized_carrier_kinds": ["registry"]
  },
  "overlays": {
    "lifecycle_status": "released"
  },
  "derivation_witness_refs": [
    "classification_policy_ref",
    "classification_policy_hash"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_with_non_blocking_gap_note",
  "gap_notes": [
    "coverage_scope is required by current coordinate doctrine but remains only externally curated here"
  ]
}
```

### 4.7 ANM Markdown Coexistence Profile Schema

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "packages/adeu_commitments_ir/schema/anm_markdown_coexistence_profile.v1.json",
  "placement_basis": "schema_kind_definition",
  "coordinate": {
    "binding_depth": "family",
    "institutional_force": "governing"
  },
  "force_profile": {
    "dominant_band": "governing",
    "support_qualifiers": ["gating"]
  },
  "carrier": {
    "carrier_superclass": "ContractGate",
    "normalized_carrier_kinds": ["contract"]
  },
  "overlays": {
    "lifecycle_status": "released"
  },
  "derivation_witness_refs": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md"
  ],
  "placement_confidence": "medium",
  "review_outcome": "accepted_curated_annotation",
  "notes": [
    "Placed as family governing because the schema defines bounded coexistence/adoption law for one released family lane rather than merely observing markdown sources"
  ]
}
```

### 4.8 Materialized Repo Schema Family Registry Snapshot

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "apps/api/fixtures/repo_description/vnext_plus99/repo_schema_family_registry_v99_reference.json",
  "placement_basis": "artifact_instance",
  "coordinate": {
    "binding_depth": "meta",
    "institutional_force": "observational"
  },
  "force_profile": {
    "dominant_band": "observational",
    "support_qualifiers": []
  },
  "coverage_scope": {
    "scope_kind": "schema_nodes",
    "covered_binding_depths": ["meta", "family", "bounded", "instance"],
    "note": "Concrete registry snapshot over schema rows; follows the current hardening-pass precedent for materialized registry instances."
  },
  "carrier": {
    "carrier_superclass": "CuratedSet",
    "normalized_carrier_kinds": ["registry", "snapshot"]
  },
  "overlays": {
    "lifecycle_status": "reference_fixture"
  },
  "derivation_witness_refs": [
    "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_with_non_blocking_gap_note",
  "gap_notes": [
    "coverage_scope remains curated externally rather than emitted inside the artifact instance"
  ]
}
```

## 5. Pilot Findings

High-confidence findings:

- the bundle already supports useful curated placement of real repo artifacts without
  geometry changes
- earlier schema-doctrine drafts fit cleanly as `meta × interpretive`
- the recursive-coordinate adoption lock fits cleanly as `meta × governing`
- the repo schema family registry remains intentionally `meta × observational` under
  the current doctrine

Non-blocking gap notes from the pilot:

- several meta observational or interpretive artifacts still need externally curated
  `coverage_scope`
- the current pilot uses report-local coordinate records rather than natively emitted
  coordinate fields on the annotated artifacts
- `anm_markdown_coexistence_profile.v1.json` is a plausible `family × governing`
  placement, but it would benefit from one later cross-check against additional
  released family schemas

## 6. Immediate Next Moves

The next bounded follow-on should be:

1. keep this seed report as the first curated placement artifact;
2. add one thinner machine-oriented coordinate registry shape later if the seed set
   proves stable;
3. only after that, wire warning-only lint around:
   - missing `placement_basis`
   - missing required `coverage_scope`
   - invalid occupancy
   - unresolved force band
   - force promotion without witness

## 7. Machine-Checkable Seed Summary

```json
{
  "schema": "recursive_coordinate_seed_placement_report@1",
  "artifact": "docs/DRAFT_RECURSIVE_COORDINATE_SEED_PLACEMENT_REPORT_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support",
  "pilot_shape_hygiene_applied": true,
  "governing_refs": [
    "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
    "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md"
  ],
  "head_commit": "598fe70e6a2139d7a0c454c7932c98286fc6cb80",
  "working_tree_state": "dirty_with_uncommitted_recursive_coordinate_bundle_docs",
  "seed_artifact_count": 8,
  "seed_records": [
    {
      "placement_subject_ref": "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
      "placement_basis": "doctrine_surface",
      "coordinate": {"binding_depth": "meta", "institutional_force": "interpretive"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
      "placement_basis": "doctrine_surface",
      "coordinate": {"binding_depth": "meta", "institutional_force": "governing"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md",
      "placement_basis": "doctrine_surface",
      "coordinate": {"binding_depth": "meta", "institutional_force": "interpretive"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "docs/DRAFT_SCHEMA_META_CORE_v0.md",
      "placement_basis": "doctrine_surface",
      "coordinate": {"binding_depth": "meta", "institutional_force": "interpretive"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
      "placement_basis": "doctrine_surface",
      "coordinate": {"binding_depth": "meta", "institutional_force": "interpretive"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json",
      "placement_basis": "schema_kind_definition",
      "coordinate": {"binding_depth": "meta", "institutional_force": "observational"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "packages/adeu_commitments_ir/schema/anm_markdown_coexistence_profile.v1.json",
      "placement_basis": "schema_kind_definition",
      "coordinate": {"binding_depth": "family", "institutional_force": "governing"},
      "placement_confidence": "medium"
    },
    {
      "placement_subject_ref": "apps/api/fixtures/repo_description/vnext_plus99/repo_schema_family_registry_v99_reference.json",
      "placement_basis": "artifact_instance",
      "coordinate": {"binding_depth": "meta", "institutional_force": "observational"},
      "placement_confidence": "high"
    }
  ],
  "non_blocking_gap_classes": [
    "missing_native_coverage_scope_on_meta_artifacts",
    "report_local_coordinate_records_only",
    "family_governing_cross_check_desirable_for_anm_profile"
  ]
}
```
