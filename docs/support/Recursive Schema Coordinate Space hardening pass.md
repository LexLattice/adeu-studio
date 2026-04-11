Result: the retained grid survives. Repo evidence does **not** force a primary-axis change. The hardening pass adds four repo-native control fields—`placement_basis`, `coverage_scope`, `force_profile`, and normalized `carrier`—plus an explicit occupancy law and transition law. No third primary axis is needed. The repo materials consistently separate core envelope from carrier/lineage overlays, distinguish interpretive from implementation authority, formalize promotion constraints, reuse phase as overlay, and treat visibility/visualization as non-authoritative surfaces rather than force bands (`docs/DRAFT_SCHEMA_META_CORE_v0.md:22-29,44-57,94-138,211-217`; `docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md:21-40,46-56,69-108,114-167`; `docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md:19-30,32-42,44-75,94-109`; `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:107-121,161-171,187-207,262-273,280-402`; `packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json:50-124`; `packages/adeu_repo_description/schema/repo_entity_catalog.v1.json:50-115`; `packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json:37-125`; `packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json:224-235,358-371`; `packages/urm_runtime/src/urm_runtime/worker_visibility.py:22-32,134-168`; `packages/urm_runtime/src/urm_runtime/topology_duty_map.py:27-34,106-125`).

## 1. RECURSIVE_COORDINATE_SYSTEM_HARDENED

The retained backbone stays intact:

* primary axes: `binding_depth × institutional_force`
* four levels per axis
* ODEU remains mandatory node-local structure
* lifecycle / visibility / trust / phase remain overlays
* derivation edges remain witness-bearing relations

The repo forces one important clarification:

**Coordinates attach to the semantic artifact role being defined or instantiated, not to storage format.**

That means:

* a doctrine doc gets the coordinate of the doctrine role it plays
* a schema definition gets the coordinate of the artifact kind it defines
* a materialized artifact gets the coordinate of the concrete artifact instance
* a meta registry or catalog that ranges over lower-depth objects must declare `coverage_scope`

That correction is repo-native, not theoretical drift. It is required because the repo already contains:

* meta descriptive registries and catalogs (`repo_schema_family_registry`, `repo_entity_catalog`)
* meta governing promotion law (`repo_descriptive_normative_binding_frame`)
* meta governing phase law (`meta_loop_sequence_contract`)
* family doctrine surfaces (`ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`)
* bounded operational contracts (`adeu_arc_task_packet`, `ux_interaction_contract`)
* instance-level advisory, governing, observational, and operative surfaces in the architecture and runtime lanes (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:280-402`; `apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json:2-9,103`; `apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json:13-17,83-97,126-156`; `packages/urm_runtime/src/urm_runtime/orchestration_state.py:358-395`).

ODEU remains local. The repo keeps internal semantic decomposition inside artifacts, not in the recursive grid: `adeu_core_ir` carries layered internal structure, and `adeu_architecture_world_hypothesis@1` already carries ontology / epistemic / deontic / utility bindings as node-local fields (`packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json:3-60`; `packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json:124-178`).

### `recursive_coordinate_system@1`

```json
{
  "schema": "recursive_coordinate_system@1",
  "system_id": "adeu_recursive_coordinate_system_hardened@1",
  "retained_backbone": {
    "primary_axes": ["binding_depth", "institutional_force"],
    "axis_depths": {"binding_depth": 4, "institutional_force": 4},
    "odeu": "mandatory_local_node_structure",
    "overlays": ["lifecycle_status", "visibility_posture", "trust_state", "phase_boundary"],
    "derivation_edges": "witness_bearing_relations"
  },
  "placement_basis_enum": [
    "doctrine_surface",
    "schema_kind_definition",
    "artifact_instance",
    "runtime_kind_definition",
    "registry_snapshot"
  ],
  "placement_basis_rule": "Coordinates attach to the semantic artifact kind defined or instantiated, not merely to storage format. Doctrine docs take the coordinate of the doctrine role they play; schema definitions take the coordinate of the artifact kind they define; materialized artifacts take the coordinate of the artifact instance they instantiate.",
  "coverage_scope_rule": "coverage_scope is required when a meta-level observational or interpretive surface ranges over lower-depth nodes or entities.",
  "rare_cell_requires_explicit_justification": true,
  "required_auxiliary_fields": [
    "placement_basis",
    "coverage_scope",
    "carrier",
    "force_profile",
    "overlays",
    "derivation_witness_refs"
  ],
  "node_local_structure": [
    "local_odeu",
    "scope_selector",
    "admissible_transformations",
    "invariants",
    "evidence_requirements",
    "deontic_constraints",
    "utility_ordering",
    "residual_seams"
  ],
  "occupancy_validation_order": [
    "base_cell_law",
    "force_profile_resolution",
    "carrier_coordinate_compatibility",
    "overlay_consistency",
    "promotion_or_derivation_witness_validation"
  ],
  "hard_rules": [
    "publicity_or_visibility_never_forms_a_primary_axis",
    "lifecycle_never_forms_a_primary_axis",
    "odeu_is_local_not_coordinate_level",
    "meta_registries_require_coverage_scope_when_they_range_over_non_meta_rows",
    "projection_may_express_but_may_not_mint_authority",
    "force_escalation_requires_explicit_promotion_witness",
    "operative_is_currently_instance_only",
    "meta_operative_is_reserved_not_currently_lawful"
  ],
  "repo_grounding_refs": [
    "docs/DRAFT_SCHEMA_META_CORE_v0.md",
    "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
    "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
    "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
    "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json",
    "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
    "packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json",
    "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json"
  ]
}
```

## 2. LAWFUL_CELL_OCCUPANCY_LAW

The space is a constrained lattice. A node is lawfully placed only if:

`base_cell is lawful`
`AND dominant force band is resolved`
`AND carrier is coordinate-compatible`
`AND overlays are consistent`
`AND any force increase is backed by a promotion witness`

Status meanings:

* `lawful_core` = normal released use
* `lawful_rare` = valid but should require explicit justification
* `invalid` = conceptually wrong under current doctrine
* `reserved` = representable in the abstract grammar but not yet authorized by repo constitution

### Occupancy matrix

| binding_depth \ institutional_force | observational | interpretive |   governing |   operative |
| ----------------------------------- | ------------: | -----------: | ----------: | ----------: |
| `meta`                              |   lawful_core |  lawful_core | lawful_core |    reserved |
| `family`                            |   lawful_core |  lawful_core | lawful_core |     invalid |
| `bounded`                           |   lawful_core |  lawful_core | lawful_core |     invalid |
| `instance`                          |   lawful_core |  lawful_rare | lawful_core | lawful_core |

Why this matrix survives repo stress-testing:

* `meta × observational` is required by schema registries and entity catalogs (`packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json:50-124`; `packages/adeu_repo_description/schema/repo_entity_catalog.v1.json:50-115`).
* `meta × interpretive` is required by meta-core and role-form doctrine drafts (`docs/DRAFT_SCHEMA_META_CORE_v0.md:22-29,36-37`; `docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md:30-40`).
* `meta × governing` is required by machine-checkable promotion law and phase contracts (`packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json:42-125`; `packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json:224-235,358-371`).
* `meta × operative` is only **reserved**, not invalid, because recursive-governance consumers are named in the binding frame, but the meta-core explicitly forbids widening into recursive amendment/mutation doctrine right now (`packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json:62-70`; `docs/DRAFT_SCHEMA_META_CORE_v0.md:211-217`).
* `family × observational`, `family × interpretive`, `family × governing` all have clean repo exemplars: family catalogs, architecture doctrine, core IR and policy registry surfaces (`packages/adeu_edge_ledger/schema/adeu_edge_class_catalog.v1.json:99-143`; `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:107-121`; `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json:3-60`; `spec/policy_registry.schema.json:4-48`).
* `family × operative` and `bounded × operative` are invalid because live control happens only at concrete run state, which the runtime lane models as instance surfaces (`packages/urm_runtime/src/urm_runtime/orchestration_state.py:358-395`).
* `bounded × interpretive` and `bounded × governing` are strongly grounded by ARC hypothesis frames and task packets, plus bounded UX contracts (`packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json:31-57,99-137`; `packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json:21-31,89-120,127-160`; `packages/adeu_core_ir/schema/ux_interaction_contract.v1.json:27-47,70-105`).
* `instance × interpretive` is rare but real: the world-hypothesis lane exists, but remains advisory and is typically promoted or blocked (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:192-199`; `apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json:2-9,103`).
* `instance × governing`, `instance × observational`, and `instance × operative` are all strongly occupied by ASIRs, manifests, settlement frames, traces/reports/attestations, and authoritative runtime state (`apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json:13-17,83-97,126-156`; `packages/adeu_architecture_compiler/schema/adeu_architecture_projection_manifest.v1.json:100-183`; `apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_analysis_settlement_frame.json:1-99`; `apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json:13-46`; `packages/adeu_agent_harness/schema/worker_execution_attestation.v1.json:28-42,70-120`; `packages/urm_runtime/src/urm_runtime/worker_visibility.py:157-168`; `packages/urm_runtime/src/urm_runtime/orchestration_state.py:358-395`).

### `lawful_cell_occupancy@1`

```json
{
  "schema": "lawful_cell_occupancy@1",
  "occupancy_law_id": "adeu_recursive_cell_occupancy_law@1",
  "status_enum": ["lawful_core", "lawful_rare", "invalid", "reserved"],
  "base_matrix": {
    "meta": {
      "observational": "lawful_core",
      "interpretive": "lawful_core",
      "governing": "lawful_core",
      "operative": "reserved"
    },
    "family": {
      "observational": "lawful_core",
      "interpretive": "lawful_core",
      "governing": "lawful_core",
      "operative": "invalid"
    },
    "bounded": {
      "observational": "lawful_core",
      "interpretive": "lawful_core",
      "governing": "lawful_core",
      "operative": "invalid"
    },
    "instance": {
      "observational": "lawful_core",
      "interpretive": "lawful_rare",
      "governing": "lawful_core",
      "operative": "lawful_core"
    }
  },
  "explicit_cases": [
    {"cell": "family:observational", "status": "lawful_core", "reason": "family catalogs and descriptive family snapshots are legitimate non-authorizing artifacts"},
    {"cell": "family:interpretive", "status": "lawful_core", "reason": "family-level hypotheses and decomposition surfaces narrow meaning without authorizing implementation"},
    {"cell": "family:governing", "status": "lawful_core", "reason": "canonical family IRs and family contracts bind downstream derivation"},
    {"cell": "family:operative", "status": "invalid", "reason": "live execution requires instance binding"},
    {"cell": "bounded:interpretive", "status": "lawful_core", "reason": "task- or program-bounded hypotheses and plans are common"},
    {"cell": "bounded:governing", "status": "lawful_core", "reason": "bounded operational contracts and task packets are common"},
    {"cell": "instance:governing", "status": "lawful_core", "reason": "manifests, settlement frames, compiled bindings, and one-run boundary contracts belong here"},
    {"cell": "instance:operative", "status": "lawful_core", "reason": "live runtime control state is instance-bound by definition"},
    {"cell": "instance:observational", "status": "lawful_core", "reason": "traces, attestations, reports, and provenance records belong here"}
  ],
  "reserved_cells": [
    {
      "cell": "meta:operative",
      "why_reserved": "The repo already names recursive-governance consumers, but the current meta core explicitly forbids widening into recursive amendment or mutation doctrine, so self-operative schema governance is representable but not yet lawful."
    }
  ],
  "invalid_cells": [
    {
      "cell": "family:operative",
      "why_invalid": "No family artifact may directly participate in one live run without concrete instance binding."
    },
    {
      "cell": "bounded:operative",
      "why_invalid": "Bounded operational grammars govern classes of cases; the live run still occurs at instance depth."
    }
  ],
  "rare_cells": [
    {
      "cell": "instance:interpretive",
      "why_rare": "Concrete candidate hypotheses and one-run interpretive settlement surfaces exist, but they are usually promoted, blocked, or superseded by governing artifacts."
    }
  ],
  "occupancy_predicate": "A node occupies its coordinate lawfully iff the base cell status is lawful_core or lawful_rare, its dominant force band is resolved, its carrier is coordinate-compatible, its overlays are consistent, and any force escalation is supported by an explicit promotion witness."
}
```

### `recursive_schema_coordinate@1`

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
    "note": "Artifact is meta-level because it classifies schemas; its coverage reaches lower-depth schema kinds."
  },
  "carrier": {
    "carrier_superclass": "CuratedSet",
    "normalized_carrier_kinds": ["registry"]
  },
  "overlays": {
    "lifecycle_status": "released",
    "visibility_posture": "internal_committed",
    "trust_state": "snapshot_bound_current",
    "phase_boundary": null
  },
  "derivation_witness_refs": [
    "classification_policy_ref",
    "classification_policy_hash"
  ],
  "placement_confidence": "high"
}
```

### Coordinate transition law

The repo already gives the transition law ingredients:

* specialization/binding narrows depth but does not mint new force
* projections may express but may not mint authority
* descriptive artifacts require separate normative authority before normative use
* execution requires settled authority before execution
* visibility / visualization surfaces are explicitly non-authoritative
* overlay changes do not relocate the node (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:163-171,205-207`; `packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json:42-125`; `apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json:4-14,29-38,74-84,98-108,122-131`; `packages/urm_runtime/src/urm_runtime/worker_visibility.py:31-32,157-160`; `packages/urm_runtime/src/urm_runtime/topology_duty_map.py:32-34,115-117`).

### `coordinate_transition_rule@1`

```json
{
  "schema": "coordinate_transition_rule@1",
  "rule_set_id": "adeu_coordinate_transition_rules@1",
  "rules": [
    {
      "rule_id": "specialize_or_bind_depth",
      "from_pattern": ["meta", "family", "bounded"],
      "to_pattern": ["family", "bounded", "instance"],
      "force_constraint": "dominant_force_must_not_increase_by_specialization_or_binding_alone",
      "allowed_if": [
        "scope_narrows_or_binds_concretely",
        "invariants_preserved",
        "evidence_requirements_preserved_or_strengthened"
      ],
      "forbidden_if": [
        "scope_widens_without_authorized_amendment",
        "specialization_claims_new_authority"
      ]
    },
    {
      "rule_id": "non_adjacent_depth_jump",
      "from_pattern": ["meta", "family"],
      "to_pattern": ["bounded", "instance"],
      "allowed_if": [
        "the jump is decomposed into explicit intermediate witnesses",
        "or an authorized exception surface records why the intermediate layer is intentionally omitted"
      ],
      "forbidden_if": [
        "intermediate binding law is silently skipped"
      ]
    },
    {
      "rule_id": "observational_to_interpretive_new_artifact",
      "from_pattern": ["observational"],
      "to_pattern": ["interpretive"],
      "depth_constraint": "same_depth_or_deeper_only",
      "allowed_if": [
        "a new interpretive artifact is emitted",
        "supporting observations are cited",
        "the new artifact remains non-authorizing until separately ratified"
      ],
      "forbidden_if": [
        "the source observational artifact is merely relabeled in place"
      ]
    },
    {
      "rule_id": "interpretive_to_governing",
      "from_pattern": ["interpretive"],
      "to_pattern": ["governing"],
      "depth_constraint": "same_depth_or_deeper_only",
      "allowed_if": [
        "explicit_ratification_or_deterministic_adjudication_exists",
        "authority_source_is_bound",
        "promotion_witness_is_recorded"
      ],
      "forbidden_if": [
        "promotion_occurs_by_projection_only",
        "promotion_occurs_by_summary_only"
      ]
    },
    {
      "rule_id": "observational_to_governing",
      "from_pattern": ["observational"],
      "to_pattern": ["governing"],
      "depth_constraint": "same_depth_or_deeper_only",
      "allowed_if": [
        "separate_normative_surface_or_lock_is_bound",
        "promotion_law_explicitly_allows_it",
        "promotion_witness_is_recorded"
      ],
      "forbidden_if": [
        "descriptive_artifact_is_treated_as_normative_by_itself",
        "eligibility_signal_is_mistaken_for_execution_approval"
      ]
    },
    {
      "rule_id": "governing_to_operative",
      "from_pattern": ["governing"],
      "to_pattern": ["operative"],
      "depth_constraint": "instance_only",
      "allowed_if": [
        "concrete_activation_or_materialization_witness_exists",
        "execution_boundary_is_bound",
        "runtime_control_state_is_actual_not_advisory"
      ],
      "forbidden_if": [
        "artifact_remains_only_manifest_or_contract",
        "state_is_non_authoritative_visualization"
      ]
    },
    {
      "rule_id": "emit_observational_sibling",
      "from_pattern": ["interpretive", "governing", "operative"],
      "to_pattern": ["observational"],
      "depth_constraint": "same_depth_or_deeper",
      "allowed_if": [
        "new_artifact_is_explicitly_trace_report_attestation_or_provenance_surface",
        "new_artifact_does_not_claim_new_authority"
      ],
      "forbidden_if": [
        "observation_output_mutates_parent_force_band_in_place"
      ]
    },
    {
      "rule_id": "overlay_change_not_coordinate_change",
      "from_pattern": ["any"],
      "to_pattern": ["same_coordinate"],
      "allowed_if": [
        "only_lifecycle_visibility_trust_or_phase_changes"
      ],
      "forbidden_if": [
        "overlay_change_is_used_to_hide_force_promotion_or_depth_change"
      ]
    }
  ]
}
```

## 3. INSTITUTIONAL_FORCE_PROFILE_MODEL

A pure scalar band is too coarse for the repo. It cannot cleanly express:

* an observational report that can block downstream action
* a governing settlement frame whose core content is chosen interpretation
* a manifest that is governing but specifically execution-binding
* an authoritative stop witness that is still evidentiary

The minimal refinement that survives repo use is:

**one dominant force band + bounded support qualifiers**

Not a third axis. Not a free vector.

Why this is the right refinement:

* the dominant band still decides cell placement
* support qualifiers do not recurse independently
* qualifiers explain mixed-use surfaces without creating axis sprawl
* every artifact still resolves to exactly one dominant band

This matches the repo’s own distinctions:

* world hypotheses are advisory only
* ASIR is authoritative
* alignment reports can be `blocked` without becoming governing
* run manifests can be authoritative stop witnesses without becoming operative
* visibility and topology maps remain derived non-authoritative views (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:163-171,192-203,332-397`; `apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json:2-9,103`; `apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json:16-46`; `apps/api/fixtures/architecture/vnext_plus88/adeu_architecture_analysis_run_manifest_v88_completed_reference.json:26-64`; `packages/urm_runtime/src/urm_runtime/worker_visibility.py:31-32,157-160`; `packages/urm_runtime/src/urm_runtime/topology_duty_map.py:32-34,115-117`).

Chosen qualifiers:

* `evidentiary`
* `interpretation_support`
* `gating`
* `execution_binding`

Every artifact must still resolve to one dominant band.

### `institutional_force_profile@1`

```json
{
  "schema": "institutional_force_profile@1",
  "model_id": "institutional_force_profile_model_hardened@1",
  "dominant_band_enum": ["observational", "interpretive", "governing", "operative"],
  "support_qualifier_enum": ["evidentiary", "interpretation_support", "gating", "execution_binding"],
  "qualifier_admissibility": {
    "observational": ["evidentiary", "gating"],
    "interpretive": ["evidentiary"],
    "governing": ["interpretation_support", "evidentiary", "gating", "execution_binding"],
    "operative": []
  },
  "dominance_resolution_order": ["operative", "governing", "interpretive", "observational"],
  "dominance_rule": "Choose the highest band the artifact can lawfully exercise by its own bound contract and declared authority source. Downstream consumers using the artifact do not by themselves raise the dominant band.",
  "support_qualifier_rule": "Support qualifiers may enrich but never replace the dominant band. Maximum two support qualifiers are allowed; otherwise the artifact should be split into separate surfaces.",
  "operative_qualifier_rule": "Dominant operative artifacts should carry no support qualifiers. If observational visibility is required, emit a sibling observational surface rather than a mixed operative-observational artifact.",
  "lawful_ambiguity_rule": "Ambiguity is lawful only at the support-qualifier layer. Every artifact must still resolve to exactly one dominant force band for coordinate placement.",
  "example_profiles": [
    {
      "artifact_kind": "world_hypothesis",
      "dominant_band": "interpretive",
      "support_qualifiers": []
    },
    {
      "artifact_kind": "analysis_settlement_frame",
      "dominant_band": "governing",
      "support_qualifiers": ["interpretation_support"]
    },
    {
      "artifact_kind": "alignment_report",
      "dominant_band": "observational",
      "support_qualifiers": ["evidentiary", "gating"]
    },
    {
      "artifact_kind": "projection_manifest",
      "dominant_band": "governing",
      "support_qualifiers": ["execution_binding"]
    },
    {
      "artifact_kind": "execution_topology_state",
      "dominant_band": "operative",
      "support_qualifiers": []
    }
  ]
}
```

### Force promotion law

The promotion law is already partially present in repo vocabulary:

* projections do not mint authority
* descriptive artifacts are not enough for normative use
* adjudication may be required before normative use
* settled authority may be required before execution (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:163-171,205-207`; `packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json:42-125`; `apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json:4-14,29-38,74-84,122-131`).

So promotion works like this:

* `observational -> interpretive`: emit a **new** interpretive artifact; do not relabel the observational one
* `interpretive -> governing`: requires ratification, lock binding, released contract, or deterministic adjudication
* `observational -> governing`: requires a separate normative surface or lock, never descriptive artifact self-promotion
* `governing -> operative`: requires concrete activation / materialization witness at instance depth only

The clean repo example is architecture compilation:
`world_hypothesis` is advisory candidate surface; `semantic_ir` is the authoritative compiled result once deterministic adjudication accepts a candidate (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:192-199`; `apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json:2-9,103`; `apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json:13-17,83-97,126-156`).

### `force_promotion_witness@1`

```json
{
  "schema": "force_promotion_witness@1",
  "witness_id": "promotion:architecture_world_hypothesis_to_semantic_ir_v86",
  "promotion_kind": "deterministic_adjudication",
  "from_coordinate": {
    "binding_depth": "instance",
    "institutional_force": "interpretive"
  },
  "to_coordinate": {
    "binding_depth": "instance",
    "institutional_force": "governing"
  },
  "source_artifact_ref": "apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json",
  "ratifying_artifact_ref": "apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json",
  "authority_source_ref": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
  "required_laws": [
    "deterministic_adjudicator_authoritative",
    "oracle_output_advisory_only",
    "accepted_candidate_lineage_required",
    "projection_may_not_mint_authority"
  ],
  "witness_evidence_refs": [
    "variant_lineage.accepted_candidate_id",
    "authority_boundary_policy",
    "semantic_hash"
  ],
  "promotion_valid": true
}
```

## 4. COORDINATE_VOCABULARY_CROSSWALK

The repo already has several authority / posture / settlement languages. They are useful, but they are not all coordinates. Without a crosswalk, the repo will drift into semantic bilingualism.

The key repo-native result:

* `institutional_force` is **not** the same as `classification_posture`
* `institutional_force` is **not** the same as `governance_posture`
* `binding_depth` is **not** the same as `family_cluster`
* `phase_boundary` is an overlay, not a coordinate
* `promotion_law_posture` is a promotion-law input, not a coordinate
* `claim_posture`, `compile_entitlement`, and `alignment_posture` are local epistemic/gating fields, not base coordinates (`docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md:46-56,133-167`; `packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json:61-124`; `packages/adeu_repo_description/schema/repo_entity_catalog.v1.json:72-103`; `packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json:42-125`; `packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json:224-235`; `packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json:31-57,99-137`; `apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_analysis_settlement_frame.json:86-99`; `apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json:16-46`).

Two especially important repo drift findings:

1. `repo_entity_catalog.governance_posture` is a free string and is too overloaded to reuse as the new coordinate vocabulary (`packages/adeu_repo_description/schema/repo_entity_catalog.v1.json:80-103`).
2. The reference entity catalog uses `descriptive_registry_row` even for surfaces whose semantic roles differ sharply, including contract surfaces, which proves the field is not a reliable force classifier (`apps/api/fixtures/repo_description/vnext_plus99/repo_entity_catalog_v99_reference.json:11-120`).

### `coordinate_vocabulary_crosswalk@1`

```json
{
  "schema": "coordinate_vocabulary_crosswalk@1",
  "crosswalk_id": "adeu_coordinate_vocab_crosswalk@1",
  "rows": [
    {
      "existing_surface": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
      "field_or_term": "lock_docs",
      "maps_to": "institutional_force=governing plus separate lifecycle/release overlays",
      "correspondence_kind": "partial",
      "action": "keep_term_but_crosswalk",
      "notes": "Binding depth must still be determined separately."
    },
    {
      "existing_surface": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
      "field_or_term": "architecture_and_decomposition_docs",
      "maps_to": "institutional_force=interpretive",
      "correspondence_kind": "partial",
      "action": "keep_term_but_crosswalk",
      "notes": "These docs are interpretively authoritative but not implementation-authoritative."
    },
    {
      "existing_surface": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
      "field_or_term": "planning_docs",
      "maps_to": "institutional_force=interpretive with lifecycle/planning overlays",
      "correspondence_kind": "partial",
      "action": "keep_term_but_crosswalk",
      "notes": "Planning status does not itself determine depth or force promotion."
    },
    {
      "existing_surface": "docs/DRAFT_INTENT_AUTHORITY_LAYERING_NOTE_v0.md",
      "field_or_term": "support_docs",
      "maps_to": "institutional_force=observational_or_interpretive depending content",
      "correspondence_kind": "partial",
      "action": "keep_term_but_crosswalk",
      "notes": "Support documents define method discipline and claim hygiene, not lock-level authority."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json",
      "field_or_term": "classification_posture",
      "maps_to": "epistemic_settlement_overlay",
      "correspondence_kind": "non_equivalent",
      "action": "retain_as_overlay",
      "notes": "Observed or settled classification posture is not the same thing as institutional force."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json",
      "field_or_term": "binding_posture",
      "maps_to": "force_promotion_and_consumer_gate_law",
      "correspondence_kind": "partial",
      "action": "crosswalk_to_promotion_law",
      "notes": "Advisory-only and adjudication-required govern how force may be used, not where the artifact is placed."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json",
      "field_or_term": "authority_source_kind",
      "maps_to": "force_promotion_witness.requirements",
      "correspondence_kind": "partial",
      "action": "crosswalk_to_promotion_law",
      "notes": "Separate lock or separate decision requirements do not create a coordinate by themselves."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json",
      "field_or_term": "promotion_law_posture",
      "maps_to": "force_promotion_witness.policy_gate",
      "correspondence_kind": "exact",
      "action": "retain_and_bind",
      "notes": "This vocabulary directly informs lawful force promotion."
    },
    {
      "existing_surface": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
      "field_or_term": "family_cluster",
      "maps_to": "lineage_or_family_grouping",
      "correspondence_kind": "non_equivalent",
      "action": "retain_as_non_coordinate_taxonomy",
      "notes": "Family cluster is grouping, not binding depth."
    },
    {
      "existing_surface": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
      "field_or_term": "lineage_overlay",
      "maps_to": "lineage_overlay",
      "correspondence_kind": "exact",
      "action": "retain_as_non_coordinate_taxonomy",
      "notes": "Lineage overlay is orthogonal taxonomy, not recursive coordinate."
    },
    {
      "existing_surface": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
      "field_or_term": "primary_carrier_class",
      "maps_to": "carrier_superclass",
      "correspondence_kind": "exact",
      "action": "retain_and_bind",
      "notes": "Used in the carrier compatibility layer, not as a coordinate."
    },
    {
      "existing_surface": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
      "field_or_term": "secondary_role_form_tags",
      "maps_to": "normalized_carrier_kinds",
      "correspondence_kind": "partial",
      "action": "retain_but_extend",
      "notes": "Repo evidence requires extra tags such as attestation, provenance, state, topology, and ledger."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
      "field_or_term": "governance_posture",
      "maps_to": "institutional_force plus overlays plus promotion law",
      "correspondence_kind": "deprecated_overlap",
      "action": "required_refactor",
      "notes": "The current field is free-string and overloaded."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
      "field_or_term": "derivation_posture",
      "maps_to": "derivation_edge_or_epistemic_overlay",
      "correspondence_kind": "partial",
      "action": "required_refactor",
      "notes": "Derivation posture is not a primary coordinate."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
      "field_or_term": "mutation_posture",
      "maps_to": "deontic_or_lifecycle_overlay",
      "correspondence_kind": "partial",
      "action": "required_refactor",
      "notes": "Mutation posture belongs to permissions or lifecycle, not coordinate placement."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
      "field_or_term": "semantic_role",
      "maps_to": "carrier_and_support_qualifier_hint",
      "correspondence_kind": "partial",
      "action": "crosswalk_but_do_not_reuse_as_coordinate",
      "notes": "contract_surface or adjudication_surface helps resolve carrier, not depth or force by itself."
    },
    {
      "existing_surface": "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
      "field_or_term": "surface_kind",
      "maps_to": "storage_or_materialization_descriptor",
      "correspondence_kind": "non_equivalent",
      "action": "retain_as_non_coordinate_descriptor",
      "notes": "Schema versus runtime file kind does not decide coordinate placement."
    },
    {
      "existing_surface": "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json",
      "field_or_term": "phase_boundary",
      "maps_to": "phase_boundary_overlay",
      "correspondence_kind": "exact",
      "action": "retain_and_bind",
      "notes": "Phase is an overlay reused by architecture IR and not a new axis."
    },
    {
      "existing_surface": "packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json",
      "field_or_term": "claim_posture",
      "maps_to": "node_local_epistemic_register_or_trust_overlay",
      "correspondence_kind": "non_equivalent",
      "action": "retain_as_local_epistemic_field",
      "notes": "Observed or inferred claim posture classifies claims inside the frame, not institutional force."
    },
    {
      "existing_surface": "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_analysis_settlement_frame.json",
      "field_or_term": "compile_entitlement",
      "maps_to": "gating_overlay_or_consumer_gate_result",
      "correspondence_kind": "partial",
      "action": "retain_as_overlay",
      "notes": "Entitled or blocked controls consumption and promotion readiness, not base coordinate."
    },
    {
      "existing_surface": "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json",
      "field_or_term": "alignment_posture",
      "maps_to": "observational_result_with_gating_support",
      "correspondence_kind": "partial",
      "action": "retain_as_local_result_field",
      "notes": "Blocked alignment does not make the report governing."
    },
    {
      "existing_surface": "apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json",
      "field_or_term": "authoritative=false",
      "maps_to": "institutional_force!=governing_or_operative",
      "correspondence_kind": "partial",
      "action": "crosswalk_to_force",
      "notes": "Non-authoritative can still mean observational or interpretive."
    },
    {
      "existing_surface": "apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json",
      "field_or_term": "authority_posture=authoritative_semantic_surface",
      "maps_to": "local_surface_authority_semantics",
      "correspondence_kind": "partial",
      "action": "keep_local_not_global",
      "notes": "This is node-local surface semantics inside ASIR, not the repo-wide coordinate by itself."
    },
    {
      "existing_surface": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
      "field_or_term": "projections_may_express_but_may_not_mint_authority",
      "maps_to": "coordinate_transition_rule.no_authority_minting",
      "correspondence_kind": "exact",
      "action": "retain_and_bind",
      "notes": "Directly constrains force promotion."
    },
    {
      "existing_surface": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
      "field_or_term": "deterministic_adjudicator_authoritative",
      "maps_to": "force_promotion_witness.allowed_authority_source",
      "correspondence_kind": "exact",
      "action": "retain_and_bind",
      "notes": "Directly authorizes interpretive-to-governing promotion through deterministic adjudication."
    },
    {
      "existing_surface": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
      "field_or_term": "oracle_output_advisory_only",
      "maps_to": "institutional_force_cap_at_interpretive_unless_separately_ratified",
      "correspondence_kind": "exact",
      "action": "retain_and_bind",
      "notes": "Prevents advisory candidate surfaces from self-promoting."
    },
    {
      "existing_surface": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
      "field_or_term": "settlement_or_observed_or_intended_or_alignment_lane",
      "maps_to": "process_lane_overlay",
      "correspondence_kind": "non_equivalent",
      "action": "retain_as_overlay",
      "notes": "Lanes structure the analysis pipeline, not the base coordinate."
    }
  ]
}
```

## 5. CARRIER_KIND_COORDINATE_COMPATIBILITY

Carrier kind remains a compatibility filter, not a hidden third axis.

Why:

* the same carrier kind can appear in different cells
* the same cell can host different carrier kinds
* some carrier kinds are only weak hints and require semantic-function resolution

The repo already proves this:

* `registry` is usually observational, but `policy_registry@1` is registry-shaped **and** governing because its primary role is normative policy, not descriptive cataloging (`spec/policy_registry.schema.json:4-48`; `apps/api/fixtures/repo_description/vnext_plus99/repo_schema_family_registry_v99_reference.json:4506-4531`).
* `runtime_state` can be operative (`ExecutionTopologyState`, `WriteLeaseState`) or observational when it is explicitly a derived non-authoritative visibility / visualization surface (`WorkerVisibilityState`, `TopologyDutyMapState`) (`packages/urm_runtime/src/urm_runtime/orchestration_state.py:358-395`; `packages/urm_runtime/src/urm_runtime/worker_visibility.py:31-32,143-168`; `packages/urm_runtime/src/urm_runtime/topology_duty_map.py:32-34,115-125`).

The repo also forces stronger normalization. Current extraction is still substring-driven and checks `log` before `catalog`, which can misclassify `*catalog` names as `TraceRecord`. It also lacks normalized tags for attestation, provenance, state, topology, and ledger (`packages/adeu_repo_description/src/adeu_repo_description/extract.py:162-204`). The role-form registry already gives the correct precedence discipline: structural signature first, semantic function second, governance role third, lexical naming last (`docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md:114-127`).

### `carrier_kind_registry@1`

```json
{
  "schema": "carrier_kind_registry@1",
  "registry_id": "adeu_carrier_kind_registry_hardened@1",
  "retained_superclasses": [
    "IntakeFrame",
    "TraceRecord",
    "CuratedSet",
    "Adjudication",
    "ContractGate",
    "StructuralModel"
  ],
  "normalized_leaf_kinds": [
    {"kind": "packet", "superclass": "IntakeFrame"},
    {"kind": "frame", "superclass": "IntakeFrame"},
    {"kind": "request", "superclass": "IntakeFrame"},
    {"kind": "candidate", "superclass": "IntakeFrame"},
    {"kind": "trace", "superclass": "TraceRecord"},
    {"kind": "record", "superclass": "TraceRecord"},
    {"kind": "log", "superclass": "TraceRecord"},
    {"kind": "token", "superclass": "TraceRecord"},
    {"kind": "provenance", "superclass": "TraceRecord"},
    {"kind": "ledger", "superclass": "TraceRecord"},
    {"kind": "bundle", "superclass": "CuratedSet"},
    {"kind": "manifest", "superclass": "CuratedSet"},
    {"kind": "registry", "superclass": "CuratedSet"},
    {"kind": "catalog", "superclass": "CuratedSet"},
    {"kind": "table", "superclass": "CuratedSet"},
    {"kind": "glossary", "superclass": "CuratedSet"},
    {"kind": "snapshot", "superclass": "CuratedSet"},
    {"kind": "report", "superclass": "Adjudication"},
    {"kind": "diagnostics", "superclass": "Adjudication"},
    {"kind": "resolution", "superclass": "Adjudication"},
    {"kind": "evidence", "superclass": "Adjudication"},
    {"kind": "result", "superclass": "Adjudication"},
    {"kind": "explain", "superclass": "Adjudication"},
    {"kind": "attestation", "superclass": "Adjudication"},
    {"kind": "contract", "superclass": "ContractGate"},
    {"kind": "policy", "superclass": "ContractGate"},
    {"kind": "gate", "superclass": "ContractGate"},
    {"kind": "binding", "superclass": "ContractGate"},
    {"kind": "ir", "superclass": "StructuralModel"},
    {"kind": "graph", "superclass": "StructuralModel"},
    {"kind": "payload", "superclass": "StructuralModel"},
    {"kind": "delta", "superclass": "StructuralModel"},
    {"kind": "projection", "superclass": "StructuralModel"},
    {"kind": "plan", "superclass": "StructuralModel"},
    {"kind": "topology", "superclass": "StructuralModel"},
    {"kind": "state", "superclass": "StructuralModel"},
    {"kind": "runtime_state", "superclass": "StructuralModel", "alias_of": "state"}
  ],
  "normalization_required_because": [
    "current_extractor_uses_substring_heuristics_only",
    "catalog_names_contain_log_and_can_false_match_trace_record",
    "repo_contains_attestation_and_provenance_surfaces_not_covered_by_current_leaf_tags",
    "repo_contains_state_and_topology_surfaces_not_covered_by_current_leaf_tags"
  ],
  "classification_precedence_rule": "Resolve carrier by structural signature first, semantic function second, governance role third, lexical naming last.",
  "example_collision_cases": [
    "packages/adeu_edge_ledger/schema/adeu_edge_class_catalog.v1.json",
    "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
    "packages/adeu_repo_description/schema/repo_symbol_catalog.v1.json"
  ],
  "example_missing_kind_cases": [
    "packages/adeu_agent_harness/schema/worker_execution_attestation.v1.json",
    "packages/adeu_agent_harness/schema/worker_execution_provenance.v1.json",
    "packages/urm_runtime/src/urm_runtime/worker_visibility.py",
    "packages/urm_runtime/src/urm_runtime/topology_duty_map.py"
  ]
}
```

### `carrier_coordinate_compatibility@1`

```json
{
  "schema": "carrier_coordinate_compatibility@1",
  "compatibility_id": "adeu_carrier_coordinate_compatibility@1",
  "not_a_primary_axis": true,
  "fallback_resolution_rule": "When a carrier kind lacks a strong default cell, resolve coordinate by semantic function and force profile using precedence structural signature > semantic function > governance role > lexical naming.",
  "rules": [
    {
      "carrier_kind": "registry",
      "carrier_superclass": "CuratedSet",
      "default_coordinate_patterns": ["meta:observational", "family:observational"],
      "conditional_cells": [
        {
          "cell": "bounded:observational",
          "allowed_if": "the registry is scoped to one bounded operational subcorpus"
        },
        {
          "cell": "family:governing",
          "allowed_if": "the primary carrier superclass is ContractGate and registry is secondary form only"
        },
        {
          "cell": "bounded:governing",
          "allowed_if": "the registry is a released policy or rule registry over a bounded operational class"
        }
      ],
      "forbidden_cells": ["instance:operative", "family:operative", "bounded:operative"],
      "default_force_profile": {"dominant_band": "observational", "support_qualifiers": []},
      "default_overlays": {"trust_state": "snapshot_bound_or_hash_bound"}
    },
    {
      "carrier_kind": "manifest",
      "carrier_superclass": "CuratedSet",
      "default_coordinate_patterns": ["instance:governing"],
      "conditional_cells": [
        {
          "cell": "family:governing",
          "allowed_if": "the artifact defines a reusable manifest family rather than one emitted manifest instance"
        },
        {
          "cell": "bounded:governing",
          "allowed_if": "the manifest constrains one bounded operational class rather than one run"
        }
      ],
      "forbidden_cells": ["instance:operative", "family:operative", "bounded:operative"],
      "default_force_profile": {"dominant_band": "governing", "support_qualifiers": ["execution_binding"]},
      "default_overlays": {"phase_boundary": "artifact_generation_or_evidence_gate"}
    },
    {
      "carrier_kind": "trace",
      "carrier_superclass": "TraceRecord",
      "default_coordinate_patterns": ["instance:observational"],
      "conditional_cells": [
        {
          "cell": "family:observational",
          "allowed_if": "the artifact defines a released trace family"
        },
        {
          "cell": "bounded:observational",
          "allowed_if": "the artifact is a schema surface defining trace records for one bounded class of runs"
        }
      ],
      "forbidden_cells": ["governing:any", "operative:any"],
      "default_force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
      "default_overlays": {"phase_boundary": "post_generation_validation_or_evidence_gate"}
    },
    {
      "carrier_kind": "contract",
      "carrier_superclass": "ContractGate",
      "default_coordinate_patterns": ["meta:governing", "family:governing", "bounded:governing"],
      "conditional_cells": [
        {
          "cell": "instance:governing",
          "allowed_if": "the contract binds one concrete run, manifest, or boundary instance"
        }
      ],
      "forbidden_cells": ["observational:any", "interpretive:any", "family:operative", "bounded:operative", "meta:operative"],
      "default_force_profile": {"dominant_band": "governing", "support_qualifiers": []},
      "default_overlays": {"lifecycle_status": "released_or_locked"}
    },
    {
      "carrier_kind": "runtime_state",
      "carrier_superclass": "StructuralModel",
      "default_coordinate_patterns": ["instance:operative"],
      "conditional_cells": [
        {
          "cell": "instance:observational",
          "allowed_if": "the state is a derived read-only visibility or visualization surface rather than the authoritative control state"
        }
      ],
      "forbidden_cells": ["meta:any", "family:any", "bounded:any"],
      "default_force_profile": {"dominant_band": "operative", "support_qualifiers": []},
      "default_overlays": {"phase_boundary": "execution"}
    },
    {
      "carrier_kind": "attestation",
      "carrier_superclass": "Adjudication",
      "default_coordinate_patterns": ["instance:observational"],
      "conditional_cells": [
        {
          "cell": "family:observational",
          "allowed_if": "the artifact defines a released attestation family"
        },
        {
          "cell": "bounded:observational",
          "allowed_if": "the artifact is a schema surface for one bounded attestation family"
        }
      ],
      "forbidden_cells": ["governing:any", "operative:any"],
      "default_force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary", "gating"]},
      "default_overlays": {"phase_boundary": "post_generation_validation_or_evidence_gate"}
    },
    {
      "carrier_kind": "provenance",
      "carrier_superclass": "TraceRecord",
      "default_coordinate_patterns": ["instance:observational"],
      "conditional_cells": [
        {
          "cell": "family:observational",
          "allowed_if": "the artifact defines a released provenance family"
        },
        {
          "cell": "bounded:observational",
          "allowed_if": "the artifact is a schema surface for one bounded provenance family"
        }
      ],
      "forbidden_cells": ["governing:any", "operative:any"],
      "default_force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
      "default_overlays": {"phase_boundary": "evidence_gate"}
    }
  ]
}
```

## 6. REPO_SCHEMA_PLACEMENT_REPORT

This is a representative placement pass, not full indexing.

The key repo-native stress-test result is:

* **meta** is occupied by registries, catalogs, meta doctrine, and machine-checkable promotion / phase contracts
* **family** is occupied by family doctrine, family IRs, and family policy / catalog surfaces
* **bounded** is occupied by task-class hypothesis and contract surfaces
* **instance** is where the architecture lane, worker lane, and runtime lane actually separate into interpretive / governing / observational / operative bands

One important hardening correction appears here:

**Architecture schema definitions for per-brief outputs resolve to `instance` coordinates by `placement_basis`, because the artifact kinds they define are per-brief emitted artifacts. The architecture doctrine doc remains family-level interpretive.**

That is the cleanest repo-native way to keep the grid and remove drift (`docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md:112-120,192-203,280-402`; `packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json:110-180`; `packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json:80-139,176-190`).

### `repo_schema_placement_report@1`

```json
{
  "schema": "repo_schema_placement_report@1",
  "report_id": "adeu_repo_coordinate_placement_report@1",
  "placement_basis_rules": [
    "doctrine_surface: coordinate follows the doctrine role played by the document",
    "schema_kind_definition: coordinate follows the semantic artifact kind defined by the schema",
    "artifact_instance: coordinate follows the concrete materialized artifact instance",
    "runtime_kind_definition: coordinate follows the runtime artifact kind defined by the code class"
  ],
  "placements_by_group": {
    "meta": [
      {
        "artifact_ref": "packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "meta", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "CuratedSet", "normalized_carrier_kinds": ["registry"]},
        "coverage_scope": {"scope_kind": "schema_nodes", "covered_binding_depths": ["meta", "family", "bounded", "instance"]},
        "confidence": "high",
        "rationale": "It is a registry over schema rows rather than a normative surface."
      },
      {
        "artifact_ref": "packages/adeu_repo_description/schema/repo_entity_catalog.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "meta", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "CuratedSet", "normalized_carrier_kinds": ["catalog"]},
        "coverage_scope": {"scope_kind": "schema_visible_entities", "covered_binding_depths": ["meta", "family", "bounded", "instance"]},
        "confidence": "high",
        "rationale": "It catalogs repo-visible entities and is explicitly descriptive rather than normative."
      },
      {
        "artifact_ref": "packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "meta", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": ["gating"]},
        "carrier": {"carrier_superclass": "ContractGate", "normalized_carrier_kinds": ["binding"]},
        "confidence": "high",
        "rationale": "It formalizes how descriptive artifacts may or may not be promoted into normative use."
      },
      {
        "artifact_ref": "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "meta", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "ContractGate", "normalized_carrier_kinds": ["contract"]},
        "confidence": "high",
        "rationale": "It defines the phase contract that downstream families reuse."
      },
      {
        "artifact_ref": "docs/DRAFT_SCHEMA_META_CORE_v0.md",
        "placement_basis": "doctrine_surface",
        "coordinate": {"binding_depth": "meta", "institutional_force": "interpretive"},
        "force_profile": {"dominant_band": "interpretive", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["plan"]},
        "confidence": "high",
        "rationale": "It proposes the common-envelope plus overlays hypothesis but explicitly refuses release or recursive-governance widening."
      },
      {
        "artifact_ref": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md",
        "placement_basis": "doctrine_surface",
        "coordinate": {"binding_depth": "meta", "institutional_force": "interpretive"},
        "force_profile": {"dominant_band": "interpretive", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["plan"]},
        "confidence": "high",
        "rationale": "It interprets how the registry should classify schema roles without directly authorizing release."
      },
      {
        "artifact_ref": "apps/api/fixtures/repo_description/vnext_plus99/repo_schema_family_registry_v99_reference.json",
        "placement_basis": "artifact_instance",
        "coordinate": {"binding_depth": "meta", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "CuratedSet", "normalized_carrier_kinds": ["registry"]},
        "coverage_scope": {"scope_kind": "schema_nodes", "covered_binding_depths": ["meta", "family", "bounded", "instance"]},
        "confidence": "high",
        "rationale": "This is a materialized registry snapshot over schema rows."
      }
    ],
    "family": [
      {
        "artifact_ref": "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md",
        "placement_basis": "doctrine_surface",
        "coordinate": {"binding_depth": "family", "institutional_force": "interpretive"},
        "force_profile": {"dominant_band": "interpretive", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["plan"]},
        "confidence": "high",
        "rationale": "It governs family interpretation of the architecture lane but is not itself the emitted authoritative ASIR."
      },
      {
        "artifact_ref": "packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "family", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["ir"]},
        "confidence": "high",
        "rationale": "It is a reusable root-family semantic IR rather than one concrete execution-bound artifact."
      },
      {
        "artifact_ref": "spec/policy_registry.schema.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "family", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "ContractGate", "normalized_carrier_kinds": ["policy", "registry"]},
        "confidence": "high",
        "rationale": "It is registry-shaped but normatively governs policy materialization."
      },
      {
        "artifact_ref": "packages/adeu_edge_ledger/schema/adeu_edge_class_catalog.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "family", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "CuratedSet", "normalized_carrier_kinds": ["catalog"]},
        "confidence": "medium",
        "rationale": "It catalogs edge classes for a family lane and does not itself authorize downstream mutation or execution."
      }
    ],
    "bounded": [
      {
        "artifact_ref": "packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "bounded", "institutional_force": "interpretive"},
        "force_profile": {"dominant_band": "interpretive", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "IntakeFrame", "normalized_carrier_kinds": ["frame"]},
        "confidence": "high",
        "rationale": "It structures bounded ARC hypothesis formation with claim postures and deontic admissibility."
      },
      {
        "artifact_ref": "packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "bounded", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "IntakeFrame", "normalized_carrier_kinds": ["packet"]},
        "confidence": "high",
        "rationale": "It binds one bounded operational class by fixing legal action envelope and boundary policy."
      },
      {
        "artifact_ref": "packages/adeu_core_ir/schema/ux_interaction_contract.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "bounded", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "ContractGate", "normalized_carrier_kinds": ["contract"]},
        "confidence": "high",
        "rationale": "It constrains one bounded UX interaction family and explicitly forbids authority inflation from UI surfaces."
      }
    ],
    "instance_interpretive": [
      {
        "artifact_ref": "packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "interpretive"},
        "force_profile": {"dominant_band": "interpretive", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "IntakeFrame", "normalized_carrier_kinds": ["candidate"]},
        "confidence": "high",
        "rationale": "It defines a per-brief candidate world artifact that is advisory only."
      },
      {
        "artifact_ref": "apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json",
        "placement_basis": "artifact_instance",
        "coordinate": {"binding_depth": "instance", "institutional_force": "interpretive"},
        "force_profile": {"dominant_band": "interpretive", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "IntakeFrame", "normalized_carrier_kinds": ["candidate"]},
        "confidence": "high",
        "rationale": "This concrete candidate is explicitly non-authoritative."
      }
    ],
    "instance_governing": [
      {
        "artifact_ref": "packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["ir"]},
        "confidence": "high",
        "rationale": "It defines the authoritative per-brief semantic root artifact."
      },
      {
        "artifact_ref": "apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json",
        "placement_basis": "artifact_instance",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["ir"]},
        "confidence": "high",
        "rationale": "This concrete ASIR binds accepted candidate lineage and authoritative semantic surface."
      },
      {
        "artifact_ref": "packages/adeu_architecture_compiler/schema/adeu_architecture_projection_manifest.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": ["execution_binding"]},
        "carrier": {"carrier_superclass": "CuratedSet", "normalized_carrier_kinds": ["manifest"]},
        "confidence": "high",
        "rationale": "It binds one concrete emission map from ASIR units to generated artifacts."
      },
      {
        "artifact_ref": "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_analysis_settlement_frame.json",
        "placement_basis": "artifact_instance",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": ["interpretation_support"]},
        "carrier": {"carrier_superclass": "IntakeFrame", "normalized_carrier_kinds": ["frame"]},
        "confidence": "high",
        "rationale": "It captures chosen interpretation and compile entitlement under a request-bound authority surface."
      },
      {
        "artifact_ref": "packages/adeu_agent_harness/schema/compiled_policy_taskpack_binding.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": ["execution_binding"]},
        "carrier": {"carrier_superclass": "ContractGate", "normalized_carrier_kinds": ["binding"]},
        "confidence": "high",
        "rationale": "It defines the compiled binding that binds one taskpack execution boundary."
      },
      {
        "artifact_ref": "packages/adeu_agent_harness/schema/task_run_boundary_instance.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": ["execution_binding"]},
        "carrier": {"carrier_superclass": "ContractGate", "normalized_carrier_kinds": ["binding"]},
        "confidence": "high",
        "rationale": "It defines the concrete run-boundary artifact over one compiled binding and taskpack manifest."
      },
      {
        "artifact_ref": "apps/api/fixtures/architecture/vnext_plus88/adeu_architecture_analysis_run_manifest_v88_completed_reference.json",
        "placement_basis": "artifact_instance",
        "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
        "force_profile": {"dominant_band": "governing", "support_qualifiers": ["evidentiary"]},
        "carrier": {"carrier_superclass": "CuratedSet", "normalized_carrier_kinds": ["manifest"]},
        "confidence": "high",
        "rationale": "The architecture doctrine explicitly treats it as an authoritative stop witness over one run."
      }
    ],
    "instance_observational": [
      {
        "artifact_ref": "packages/adeu_architecture_compiler/schema/adeu_architecture_observation_frame.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
        "carrier": {"carrier_superclass": "IntakeFrame", "normalized_carrier_kinds": ["frame"]},
        "confidence": "high",
        "rationale": "It defines the observed implementation facts lane and carries no intended authority."
      },
      {
        "artifact_ref": "packages/adeu_architecture_compiler/schema/adeu_architecture_conformance_report.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary", "gating"]},
        "carrier": {"carrier_superclass": "Adjudication", "normalized_carrier_kinds": ["report"]},
        "confidence": "high",
        "rationale": "It reports validator output and readiness classification without itself minting authority."
      },
      {
        "artifact_ref": "packages/adeu_architecture_compiler/schema/adeu_architecture_checkpoint_trace.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
        "carrier": {"carrier_superclass": "TraceRecord", "normalized_carrier_kinds": ["trace"]},
        "confidence": "high",
        "rationale": "It records hybrid checkpoint and adjudication lineage but does not replace the governing semantic surface."
      },
      {
        "artifact_ref": "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json",
        "placement_basis": "artifact_instance",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary", "gating"]},
        "carrier": {"carrier_superclass": "Adjudication", "normalized_carrier_kinds": ["report"]},
        "confidence": "high",
        "rationale": "It can block downstream use by reporting a blocking finding, but it remains a report rather than a governing contract."
      },
      {
        "artifact_ref": "packages/adeu_agent_harness/schema/worker_execution_attestation.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary", "gating"]},
        "carrier": {"carrier_superclass": "Adjudication", "normalized_carrier_kinds": ["attestation"]},
        "confidence": "high",
        "rationale": "It records validator-bound execution attestation and prompt authority posture rather than live control authority."
      },
      {
        "artifact_ref": "packages/adeu_agent_harness/schema/worker_execution_provenance.v1.json",
        "placement_basis": "schema_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
        "carrier": {"carrier_superclass": "TraceRecord", "normalized_carrier_kinds": ["provenance"]},
        "confidence": "high",
        "rationale": "It records run provenance for one boundary instance."
      },
      {
        "artifact_ref": "packages/urm_runtime/src/urm_runtime/worker_visibility.py#WorkerVisibilityState",
        "placement_basis": "runtime_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["runtime_state"]},
        "confidence": "high",
        "rationale": "Its own authority policies say visibility alone confers no acceptance authority and self-report stays non-authoritative until reconciled."
      },
      {
        "artifact_ref": "packages/urm_runtime/src/urm_runtime/topology_duty_map.py#TopologyDutyMapState",
        "placement_basis": "runtime_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
        "force_profile": {"dominant_band": "observational", "support_qualifiers": ["evidentiary"]},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["topology", "runtime_state"]},
        "confidence": "high",
        "rationale": "Its own policy says it is a derived non-authoritative visualization from canonical execution state."
      }
    ],
    "instance_operative": [
      {
        "artifact_ref": "packages/urm_runtime/src/urm_runtime/orchestration_state.py#ExecutionTopologyState",
        "placement_basis": "runtime_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "operative"},
        "force_profile": {"dominant_band": "operative", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["runtime_state", "topology"]},
        "confidence": "high",
        "rationale": "It is the canonical runtime execution topology state rather than a derived visualization."
      },
      {
        "artifact_ref": "packages/urm_runtime/src/urm_runtime/orchestration_state.py#WriteLeaseState",
        "placement_basis": "runtime_kind_definition",
        "coordinate": {"binding_depth": "instance", "institutional_force": "operative"},
        "force_profile": {"dominant_band": "operative", "support_qualifiers": []},
        "carrier": {"carrier_superclass": "StructuralModel", "normalized_carrier_kinds": ["runtime_state", "state"]},
        "confidence": "high",
        "rationale": "It carries active authoritative writer state and live lease control."
      }
    ]
  },
  "minimal_repo_correction": [
    "coordinates must attach to semantic artifact role rather than storage format",
    "meta observational registries and catalogs require explicit coverage_scope",
    "architecture schema definitions for per-brief emitted artifacts resolve to instance coordinates by placement_basis, while architecture doctrine docs remain family-level interpretive surfaces"
  ],
  "known_remaining_ambiguities": [
    "some catalog- and frame-shaped schema definitions still need explicit placement_basis to avoid being read by filename alone",
    "free-string governance_posture remains too overloaded to auto-derive coordinates safely"
  ]
}
```

## 7. HARDENING_GAP_REPORT_AGAINST_CURRENT_COORDINATE_DOC

The earlier coordinate document was correct on the big geometry. The gaps were operational, not axial.

Closed gaps:

1. **lawful occupancy** is now explicit
2. **force ambiguity** is now formalized as dominant band + support qualifiers
3. **vocabulary coexistence** is now crosswalked
4. **carrier compatibility** is now normalized without becoming a third axis
5. **repo grounding** is now demonstrated on real artifacts

Minimal repo-forced corrections:

* add `placement_basis`
* add `coverage_scope` for meta registries and catalogs
* normalize carrier kinds beyond substring heuristics
* treat force ambiguity as `dominant_band + support_qualifiers`, not as extra axes or free-string posture drift

The largest remaining repo drift risks are not in the grid itself; they are in legacy vocabulary surfaces and extraction heuristics (`packages/adeu_repo_description/schema/repo_entity_catalog.v1.json:72-103`; `packages/adeu_repo_description/src/adeu_repo_description/extract.py:162-204`; `apps/api/fixtures/repo_description/vnext_plus99/repo_entity_catalog_v99_reference.json:11-120`).

### `coordinate_hardening_report@1`

```json
{
  "schema": "coordinate_hardening_report@1",
  "report_id": "recursive_coordinate_hardening_gap_report@1",
  "retained_backbone_changed": false,
  "axis_change_required": false,
  "closed_gaps": [
    {
      "gap": "lawful_cell_occupancy",
      "status": "closed",
      "resolution": "explicit base matrix plus compatibility and promotion filters"
    },
    {
      "gap": "institutional_force_ambiguity",
      "status": "closed",
      "resolution": "dominant force band plus bounded support qualifiers"
    },
    {
      "gap": "vocabulary_crosswalk",
      "status": "closed",
      "resolution": "explicit mapping between coordinate language and repo vocabularies"
    },
    {
      "gap": "carrier_kind_coordinate_compatibility",
      "status": "closed",
      "resolution": "carrier registry preserved and normalized with explicit allowed cells"
    },
    {
      "gap": "repo_wide_placement_pass",
      "status": "closed",
      "resolution": "representative grounded placement report across meta, family, bounded, instance, and runtime artifacts"
    }
  ],
  "minimal_repo_forced_corrections": [
    "coordinates must attach to semantic artifact role rather than storage format",
    "meta observational registries require explicit coverage_scope",
    "carrier normalization must be extended beyond current substring heuristics",
    "force ambiguity must be recorded as dominant band plus support qualifiers rather than a second hidden posture vocabulary"
  ],
  "repo_detected_drift_risks": [
    "free-string governance_posture in repo_entity_catalog is overloaded",
    "substring-based carrier inference can misclassify catalog artifacts as trace records",
    "support and planning vocabularies can be mistaken for force bands without crosswalk discipline",
    "schema-kind definitions and materialized artifact instances can be conflated unless placement_basis is explicit"
  ],
  "recommended_next_repo_actions": [
    "add recursive_schema_coordinate records to released meta registries and key schema families",
    "replace substring-only carrier inference with precedence-based classifier",
    "add coordinate and force-profile linting to schema review",
    "bind coverage_scope explicitly on all meta observational and meta interpretive catalog surfaces",
    "refactor legacy governance_posture into canonical coordinate plus overlays plus promotion-law fields"
  ],
  "confidence": "high"
}
```

## Final hardened determination

The winning base space remains:

**`binding_depth × institutional_force`**

with:

* `binding_depth = {meta, family, bounded, instance}`
* `institutional_force = {observational, interpretive, governing, operative}`

Hardening additions:

* `placement_basis` to stop storage-format confusion
* `coverage_scope` for meta surfaces over lower-depth objects
* `force_profile = dominant_band + support_qualifiers`
* normalized `carrier` with explicit compatibility law
* explicit occupancy and transition law
* explicit vocabulary crosswalk
* grounded repo placement report

That is now strong enough to support:

* per-node coordinate records
* lawful cell validation
* force-promotion witness checks
* carrier compatibility linting
* crosswalk-driven migration from overloaded posture vocabularies
* future schema review without reopening the base geometry each time
