# Assessment vNext+77 Edges (Post Closeout)

This document records edge disposition for `vNext+77` (`V40-A` architecture
semantic-root schema/export/hash baseline) after arc closeout.

Status: post-closeout assessment (March 23, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS77_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v77_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V40-A` semantic-root baseline; canonical
  `adeu_architecture_intent_packet@1`,
  `adeu_architecture_ontology_frame@1`,
  `adeu_architecture_boundary_graph@1`,
  `adeu_architecture_world_hypothesis@1`, and
  `adeu_architecture_semantic_ir@1`; authoritative and mirrored schema exports;
  deterministic canonicalization and semantic-hash replay; root/sibling boundary
  exclusion; authority-policy propagation; advisory world-hypothesis posture; committed
  reference fixtures; and review-driven canonicalization/integrity hardening.
- Out of scope: deterministic compiler package activation, conformance-report release,
  checkpoint/oracle execution, projection bundle or manifest release, `adeu_core_ir`
  lowering, UX lowering, API/workbench surfaces, direct prompt-to-code generation, and
  any broader post-`V40-A` widening.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v17.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS77.md`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/root_family.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
- `packages/adeu_architecture_ir/tests/test_root_family.py`
- `packages/adeu_architecture_ir/tests/test_architecture_ir_export_schema.py`
- `apps/api/fixtures/architecture/vnext_plus77/`
- `artifacts/quality_dashboard_v77_closeout.json`
- `artifacts/stop_gate/metrics_v77_closeout.json`
- `artifacts/agent_harness/v77/evidence_inputs/metric_key_continuity_assertion_v77.json`
- `artifacts/agent_harness/v77/evidence_inputs/runtime_observability_comparison_v77.json`
- `artifacts/agent_harness/v77/evidence_inputs/v40a_architecture_semantic_root_evidence_v77.json`
- merged PR: `#299`

## Pre-Lock Edge Set Outcome (v77 Closeout)

1. Root artifact catch-all drift: `resolved`.
   - the released semantic root remains meaning-only and rejects downstream checkpoint,
     projection, conformance, and readiness state.
2. Package timing drift: `resolved`.
   - `packages/adeu_architecture_ir` is the only active package in v77 and
     `packages/adeu_architecture_compiler` remains deferred.
3. Advisory / authoritative collapse: `resolved`.
   - world-hypothesis artifacts remain advisory-only and canonical authority remains
     frozen to `adeu_architecture_semantic_ir@1`.
4. Hash-law drift: `resolved`.
   - semantic-hash derivation now runs over the normalized validated semantic-root
     payload rather than the raw input dict.
5. Schema overbreadth: `resolved`.
   - only the five semantic-root artifacts were released and downstream family
     surfaces remain explicit non-goals.
6. Formal sidecar authority drift: `resolved`.
   - Lean proof mirrors remain additive and non-blocking, with package schemas/tests
     staying authoritative for shipped behavior.
7. Shape-only schema baseline: `resolved`.
   - v77 now includes root-local presence rules, duplicate-id rejection, node/crossing
     reference closure, canonical set normalization, and accepted-hypothesis alignment.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/root_family.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/__init__.py`
  - `packages/adeu_architecture_ir/schema/adeu_architecture_intent_packet.v1.json`
  - `packages/adeu_architecture_ir/schema/adeu_architecture_ontology_frame.v1.json`
  - `packages/adeu_architecture_ir/schema/adeu_architecture_boundary_graph.v1.json`
  - `packages/adeu_architecture_ir/schema/adeu_architecture_world_hypothesis.v1.json`
  - `packages/adeu_architecture_ir/schema/adeu_architecture_semantic_ir.v1.json`
  - `spec/adeu_architecture_intent_packet.schema.json`
  - `spec/adeu_architecture_ontology_frame.schema.json`
  - `spec/adeu_architecture_boundary_graph.schema.json`
  - `spec/adeu_architecture_world_hypothesis.schema.json`
  - `spec/adeu_architecture_semantic_ir.schema.json`
  - `apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_intent_packet_v77_reference.json`
  - `apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_ontology_frame_v77_reference.json`
  - `apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_boundary_graph_v77_reference.json`
  - `apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_world_hypothesis_v77_reference.json`
  - `apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_semantic_ir_v77_reference.json`
- merged guard files:
  - `packages/adeu_architecture_ir/tests/test_root_family.py`
  - `packages/adeu_architecture_ir/tests/test_architecture_ir_export_schema.py`
- v77 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v40a_architecture_semantic_root_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v77/runtime/evidence/codex/copilot/v77-closeout-main-1/`
- review-driven hardening now includes:
  - crossing-id validation even without ontology-frame context,
  - stable canonical sorting for set-like lists while preserving workflow step order,
  - semantic-hash materialization from normalized validated payload,
  - exact accepted-hypothesis alignment with `variant_lineage.accepted_candidate_id`.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v77_edge_closeout_summary@1",
  "arc": "vNext+77",
  "target_path": "V40-A",
  "prelock_edge_count": 7,
  "resolved_edge_count": 7,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v76": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v77)

1. The released lane remains intentionally bounded to semantic-root substrate only and
   not deterministic compiler or projection behavior.
2. Whole-ASIR integrity, conformance reporting, and blocked/ready gating remain
   deferred by design to `V40-B`.
3. Hybrid ambiguity handling, lowerings, and UX compatibility remain excluded from the
   released baseline.
4. The Lean sidecar remains optional and proof-mirror-only until a later explicit lock
   promotes any finite-law subset further.

## Recommendation (Post Closeout)

1. Mark the v77 edge set as closed with no blocking issues.
2. Treat canonical
   `adeu_architecture_intent_packet@1`,
   `adeu_architecture_ontology_frame@1`,
   `adeu_architecture_boundary_graph@1`,
   `adeu_architecture_world_hypothesis@1`, and
   `adeu_architecture_semantic_ir@1` plus their exported schemas and v77 reference
   fixtures as the released `V40-A` substrate going forward.
3. Treat `V40-A` as complete at its bounded baseline on `main`; any additional root-only
   hardening should be justified as exceptional rather than assumed.
4. Move the next default candidate to `V40-B`, where deterministic assembly, whole-ASIR
   integrity, conformance reporting, and blocked/ready gating can be introduced without
   reopening the released root boundary.
