# Draft Recursive Coordinate Stress Cell Placement Report v0

Status: support-layer curated placement report for the missing bounded and instance
stress cells.

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

It exists to test the parts of the retained grid that Pilot 1 did not reach:

- `bounded × interpretive`
- `bounded × governing`
- `instance × interpretive`
- `instance × governing`
- `instance × observational`
- `instance × operative`

## 1. Direct Answer

The missing stress cells are occupiable on real repo artifacts without changing the
geometry.

This pilot confirms:

- `bounded × interpretive` is stable on non-committing hypothesis surfaces
- `bounded × governing` is stable on bounded legal-action and boundary-policy packets
- `instance × interpretive` is lawful-rare but stable when the artifact is explicitly
  advisory-only
- `instance × governing` is stable on authoritative per-brief semantic root artifacts
- `instance × observational` remains observational even when the report carries
  blocking findings and gating significance
- `instance × operative` is grounded on a committed materialized runtime control-state
  artifact

The important transition-law result is that bounded governing does not collapse into
instance governing by specialization alone. The packet and the accepted semantic root
remain distinct artifacts with different scope and authority.

## 2. Scope And Method

Selection rule for this pilot:

- choose one artifact per previously untested cell
- prefer files already grounded in the earlier hardening pass
- include at least one materialized artifact instance
- ground the operative cell on a committed materialized runtime control-state artifact

Placement basis meanings used here:

- `schema_kind_definition`
- `artifact_instance`

Pilot hygiene:

- `overlays` remain narrow and carry lifecycle only
- carrier labels are kept conservative
- `derivation_witness_refs` are used only for direct authority-binding or materialized
  lineage witnesses
- broader contextual grounding is described in rationale text instead of being
  overloaded into witness fields

## 3. Stress Cell Matrix

| target cell | artifact_ref | placement_basis | confidence | note |
| --- | --- | --- | --- | --- |
| `bounded × interpretive` | `packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json` | `schema_kind_definition` | `high` | non-committing investigation posture and explicit claim/deontic admissibility |
| `bounded × governing` | `packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json` | `schema_kind_definition` | `high` | bounded legal-action envelope and adapter boundary policy |
| `instance × interpretive` | `packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json` | `schema_kind_definition` | `high` | explicit `authoritative = false` and advisory-only oracle posture |
| `instance × governing` | `packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json` | `schema_kind_definition` | `high` | accepted-candidate lineage, deontic gates, and fail-closed authority boundary |
| `instance × observational` | `apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json` | `artifact_instance` | `high` | blocking findings in a report do not mint governing authority |
| `instance × operative` | `artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/write_lease_state.json` | `artifact_instance` | `high` | committed operative closeout artifact with live authoritative holder and single-writer lease control |

## 4. Curated Coordinate Records

### 4.1 Bounded × Interpretive

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json",
  "placement_basis": "schema_kind_definition",
  "coordinate": {
    "binding_depth": "bounded",
    "institutional_force": "interpretive"
  },
  "force_profile": {
    "dominant_band": "interpretive",
    "support_qualifiers": []
  },
  "carrier": {
    "carrier_superclass": "IntakeFrame",
    "normalized_carrier_kinds": ["frame"]
  },
  "overlays": {
    "lifecycle_status": "committed_current"
  },
  "derivation_witness_refs": [],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation",
  "rationale": [
    "The artifact binds claim posture and deontic admissibility while preserving non-committing investigation posture.",
    "Its explicit `action_commitment_allowed = false` and `posture_kind = non_committing_investigation` keep it interpretive rather than governing."
  ]
}
```

### 4.2 Bounded × Governing

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json",
  "placement_basis": "schema_kind_definition",
  "coordinate": {
    "binding_depth": "bounded",
    "institutional_force": "governing"
  },
  "force_profile": {
    "dominant_band": "governing",
    "support_qualifiers": []
  },
  "carrier": {
    "carrier_superclass": "IntakeFrame",
    "normalized_carrier_kinds": ["packet"]
  },
  "overlays": {
    "lifecycle_status": "committed_current"
  },
  "derivation_witness_refs": [],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation",
  "rationale": [
    "The packet fixes one bounded legal-action envelope plus adapter boundary policy.",
    "Its policy semantics are deontic and scope-bound, which is stronger than interpretation but still bounded rather than instance-root authoritative."
  ]
}
```

### 4.3 Instance × Interpretive

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json",
  "placement_basis": "schema_kind_definition",
  "coordinate": {
    "binding_depth": "instance",
    "institutional_force": "interpretive"
  },
  "force_profile": {
    "dominant_band": "interpretive",
    "support_qualifiers": []
  },
  "carrier": {
    "carrier_superclass": "IntakeFrame",
    "normalized_carrier_kinds": ["candidate"]
  },
  "overlays": {
    "lifecycle_status": "committed_current"
  },
  "derivation_witness_refs": [],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation",
  "lawful_rare_justification": [
    "The artifact is per-brief and instance-scoped, but it is explicitly advisory-only.",
    "It pins `authoritative = false` and carries `oracle_output_advisory_only` plus `projections_may_express_but_may_not_mint_authority`."
  ]
}
```

### 4.4 Instance × Governing

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json",
  "placement_basis": "schema_kind_definition",
  "coordinate": {
    "binding_depth": "instance",
    "institutional_force": "governing"
  },
  "force_profile": {
    "dominant_band": "governing",
    "support_qualifiers": []
  },
  "carrier": {
    "carrier_superclass": "StructuralModel",
    "normalized_carrier_kinds": ["ir"]
  },
  "overlays": {
    "lifecycle_status": "committed_current"
  },
  "derivation_witness_refs": [],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation",
  "rationale": [
    "The artifact binds accepted-candidate lineage and root-family canonicalization for one architecture instance.",
    "Its deontic gates and fail-closed authority boundary make it the per-brief authoritative semantic root rather than a bounded packet or advisory hypothesis."
  ]
}
```

### 4.5 Instance × Observational

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json",
  "placement_basis": "artifact_instance",
  "coordinate": {
    "binding_depth": "instance",
    "institutional_force": "observational"
  },
  "force_profile": {
    "dominant_band": "observational",
    "support_qualifiers": ["evidentiary", "gating"]
  },
  "carrier": {
    "carrier_superclass": "Adjudication",
    "normalized_carrier_kinds": ["report"]
  },
  "overlays": {
    "lifecycle_status": "reference_fixture"
  },
  "derivation_witness_refs": [
    "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_analysis_request.json",
    "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_analysis_settlement_frame.json",
    "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_observation_frame.json"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation",
  "rationale": [
    "The report carries blocking findings and gating significance, but it remains an adjudicative observation/reporting surface rather than the source of governing authority.",
    "This is the key stress-cell proof that evidentiary or gating qualifiers do not by themselves promote an observational report into a governing artifact."
  ]
}
```

### 4.6 Instance × Operative

```json
{
  "schema": "recursive_schema_coordinate@1",
  "placement_subject_ref": "artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/write_lease_state.json",
  "placement_basis": "artifact_instance",
  "coordinate": {
    "binding_depth": "instance",
    "institutional_force": "operative"
  },
  "force_profile": {
    "dominant_band": "operative",
    "support_qualifiers": []
  },
  "carrier": {
    "carrier_superclass": "StructuralModel",
    "normalized_carrier_kinds": ["payload"]
  },
  "overlays": {
    "lifecycle_status": "closeout_artifact"
  },
  "derivation_witness_refs": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md"
  ],
  "placement_confidence": "high",
  "review_outcome": "accepted_curated_annotation",
  "rationale": [
    "The materialized state carries `control_plane_owner`, `lease_transfer_policy`, `active_authoritative_writer_count`, and `current_authoritative_holder`.",
    "That is live control authority, not observation or interpretation, so the operative placement is warranted even at the committed artifact-instance level."
  ],
  "context_refs": [
    "packages/urm_runtime/src/urm_runtime/orchestration_state.py#WriteLeaseState",
    "artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/execution_topology_state.json"
  ]
}
```

## 5. Stress Findings

High-confidence findings:

- the retained geometry now has grounded examples across the previously missing bounded
  and instance cells
- the lawful-rare `instance × interpretive` cell is usable when the artifact is
  explicitly advisory-only
- observational artifacts with blocking findings still remain observational when the
  artifact itself is a report rather than a governing contract
- operative authority is grounded on a committed write-lease closeout artifact

Transition-law findings:

- bounded governing and instance governing remain distinct; one bounded packet does not
  self-promote into a per-brief authoritative semantic root
- instance observational with `gating` support qualifiers does not self-promote into
  governing
- the operative cell is now grounded at the committed artifact-instance level rather
  than only at runtime kind-definition level

## 6. Recommended Next Move

With Pilot 1 plus Pilot 2 together, the coordinate method is grounded enough for a very
small warning-only lint prototype.

The first lint slice should still stay narrow:

- missing `placement_basis`
- missing required `coverage_scope`
- invalid occupancy
- unresolved dominant force band
- force promotion claim without witness

## 7. Machine-Checkable Stress Summary

```json
{
  "schema": "recursive_coordinate_stress_cell_report@1",
  "artifact": "docs/DRAFT_RECURSIVE_COORDINATE_STRESS_CELL_PLACEMENT_REPORT_v0.md",
  "artifact_status": "draft",
  "authority_layer": "support",
  "governing_refs": [
    "docs/DRAFT_RECURSIVE_COORDINATE_CORE_BUNDLE_v0.md",
    "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
    "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md"
  ],
  "stress_cells_covered": [
    "bounded:interpretive",
    "bounded:governing",
    "instance:interpretive",
    "instance:governing",
    "instance:observational",
    "instance:operative"
  ],
  "stress_record_count": 6,
  "stress_records": [
    {
      "placement_subject_ref": "packages/adeu_arc_agi/schema/adeu_arc_hypothesis_frame.v1.json",
      "placement_basis": "schema_kind_definition",
      "coordinate": {"binding_depth": "bounded", "institutional_force": "interpretive"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json",
      "placement_basis": "schema_kind_definition",
      "coordinate": {"binding_depth": "bounded", "institutional_force": "governing"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json",
      "placement_basis": "schema_kind_definition",
      "coordinate": {"binding_depth": "instance", "institutional_force": "interpretive"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json",
      "placement_basis": "schema_kind_definition",
      "coordinate": {"binding_depth": "instance", "institutional_force": "governing"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs/adeu_architecture_alignment_report.json",
      "placement_basis": "artifact_instance",
      "coordinate": {"binding_depth": "instance", "institutional_force": "observational"},
      "placement_confidence": "high"
    },
    {
      "placement_subject_ref": "artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/write_lease_state.json",
      "placement_basis": "artifact_instance",
      "coordinate": {"binding_depth": "instance", "institutional_force": "operative"},
      "placement_confidence": "high"
    }
  ],
  "remaining_non_blocking_gap_classes": [
    "carrier_normalization_for_runtime_state_still_bounded_and_conservative"
  ]
}
```
