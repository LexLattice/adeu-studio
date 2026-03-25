# Assessment vNext+80 Edges (Post Closeout)

This document records edge disposition for `vNext+80` (`V40-D` architecture
projection bundle, manifest, and `adeu_core_ir` lowering baseline) after arc closeout.

Status: post-closeout assessment (March 25, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS80_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v80_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V40-D` lowering baseline; canonical
  `adeu_architecture_projection_bundle@1` and
  `adeu_architecture_projection_manifest@1`; deterministic lowering into
  `adeu_core_ir@0.1`; explicit projection-unit source and output lineage; bundle and
  manifest provenance; blocked-vs-ready honesty; committed ready and blocked fixture
  ladders; authoritative and mirrored schema exports; and review-driven fail-closed
  hardening.
- Out of scope: reopening `V40-A` root-family semantics, `V40-B` conformance
  semantics, or `V40-C` hybrid semantics; broader target-family lowering; UX
  compatibility release; API/workbench human-review surfaces; direct repo mutation;
  direct prompt-to-code generation; and any broader post-`V40-D` widening.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v20.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS79.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/projection.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40d.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- `apps/api/fixtures/architecture/vnext_plus80/`
- `artifacts/quality_dashboard_v80_closeout.json`
- `artifacts/stop_gate/metrics_v80_closeout.json`
- `artifacts/agent_harness/v80/evidence_inputs/metric_key_continuity_assertion_v80.json`
- `artifacts/agent_harness/v80/evidence_inputs/runtime_observability_comparison_v80.json`
- `artifacts/agent_harness/v80/evidence_inputs/v40d_architecture_core_ir_lowering_evidence_v80.json`
- merged PR: `#302`

## Pre-Lock Edge Set Outcome (v80 Closeout)

1. Lowering source-bypass drift: `resolved`.
   - the released lane binds bundle and manifest artifacts back to released `V40-A`
     semantic-root, `V40-B` conformance, and `V40-C` checkpoint lineage and rejects
     direct-from-root or free-floating lowering shortcuts.
2. Projection honesty drift: `resolved`.
   - ready units now require released conformance `ready` plus no active unit-local
     blockers, while blocked units preserve blocking refs explicitly and emit no target
     artifact refs.
3. Ghost manifest lineage: `resolved`.
   - emitted lowering artifacts now carry explicit source refs, projection ids,
     consumed root refs, and compiler provenance, and manifest validation rejects
     lineage gaps.
4. Target-family widening: `resolved`.
   - the released lane keeps `adeu_core_ir@0.1` as the only lawful target family and
     continues to defer UX and broader application-family lowering.
5. Adjudication / projection collapse: `resolved`.
   - checkpoint adjudication remains a distinct consumed input, and `escalated_human`
     lineage remains blocking at projection time rather than silently collapsing into
     ready output.
6. Edge-vocabulary inflation: `resolved`.
   - the first lowering baseline stays intentionally narrow with starter
     `depends_on`, `gates`, `serves_goal`, `prioritizes`, and `justifies` edges only.
7. Blocked output surface inflation: `resolved`.
   - blocked projection units now carry `output_artifact_refs = []`, and committed
     blocked-honesty fixtures plus tests preserve that exact non-emitting law.
8. Formal-sidecar timing drift: `resolved`.
   - the Lean lane remains parallel and non-authoritative; the merged `V40-D` surface
     is fully carried by the Python implementation, schemas, fixtures, and evidence on
     `main`.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/projection.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
  - `packages/adeu_architecture_compiler/schema/adeu_architecture_projection_bundle.v1.json`
  - `packages/adeu_architecture_compiler/schema/adeu_architecture_projection_manifest.v1.json`
  - `spec/adeu_architecture_projection_bundle.schema.json`
  - `spec/adeu_architecture_projection_manifest.schema.json`
  - committed v80 fixture ladder under `apps/api/fixtures/architecture/vnext_plus80/`
- merged guard files:
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40d.py`
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- v80 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v40d_architecture_core_ir_lowering_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v80/runtime/evidence/codex/copilot/v80-closeout-main-1/`
- review-driven hardening now includes:
  - ready output refs are bound to exact emitted `adeu_core_ir` lineage,
  - manifest validation preserves blocker and readiness consistency rather than only
    top-level lineage,
  - maintainability cleanup landed without relaxing the lowering-law surface.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v80_edge_closeout_summary@1",
  "arc": "vNext+80",
  "target_path": "V40-D",
  "prelock_edge_count": 8,
  "resolved_edge_count": 8,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v79": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v80)

1. The released lane remains intentionally bounded to one honest `adeu_core_ir@0.1`
   lowering and not broader target-family release.
2. UX compatibility surfaces, workbench/API review routes, and broader application
   target families remain deferred by design to later `V40-E` / `V40-F` work.
3. The formal Lean sidecar remains optional and proof-mirror-only until a later
   explicit lock promotes any finite-law subset further.
4. Family-complete evidence/release wiring remains intentionally deferred beyond the
   first lowering baseline.

## Recommendation (Post Closeout)

1. Mark the v80 edge set as closed with no blocking issues.
2. Treat canonical projection bundle, projection manifest, and authoritative
   `adeu_core_ir@0.1` ready-lowering plus their authoritative and mirrored schema
   exports and committed v80 fixtures as the released `V40-D` lowering substrate going
   forward.
3. Treat `V40-D` as complete at its bounded baseline on `main`; any additional
   lowering-only hardening should be justified as exceptional rather than assumed.
4. Move the next default candidate to `V40-E`, where UX compatibility can be
   introduced without reopening the released semantic-root, conformance, hybrid, or
   lowering boundaries.
