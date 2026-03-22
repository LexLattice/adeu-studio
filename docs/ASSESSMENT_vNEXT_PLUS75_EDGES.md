# Assessment vNext+75 Edges (Post Closeout)

This document records edge disposition for `vNext+75` (`V39-D` synthetic
pressure-mismatch fix-plan and policy-projection baseline) after arc closeout.

Status: post-closeout assessment (March 22, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS75_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v75_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V39-D` pressure-mismatch fix-plan baseline; canonical
  `synthetic_pressure_mismatch_fix_plan@1`; authoritative and mirrored schema exports;
  committed local fix-plan fixtures; deterministic replay from released v74
  conformance reports; structurally separate forward-agent and post-optimizer
  projections; candidate-only safe-autofix planning; and closeout evidence/guard
  coverage.
- Out of scope: patch generation, automatic repo mutation, detector reruns, raw-subject
  planning bypass, hybrid oracle request/resolution/checkpoint artifacts, repo-wide
  scanning, workflow-blocking policy automation, authorship classification, and any
  broader `V39-E` widening.

## Inputs

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v15.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md`
- `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_fix_plan.py`
- `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_fix_plan.py`
- `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py`
- `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus75/`
- `artifacts/quality_dashboard_v75_closeout.json`
- `artifacts/stop_gate/metrics_v75_closeout.json`
- `artifacts/agent_harness/v75/evidence_inputs/metric_key_continuity_assertion_v75.json`
- `artifacts/agent_harness/v75/evidence_inputs/runtime_observability_comparison_v75.json`
- `artifacts/agent_harness/v75/evidence_inputs/v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json`
- merged PR: `#297`

## Pre-Lock Edge Set Outcome (v75 Closeout)

1. Plan / execution collapse: `resolved`.
   - released fix plans remain advisory-only and do not authorize patch payloads,
     repo mutation, or executable edit instructions.
2. Role-collapse drift: `resolved`.
   - forward-agent and post-optimizer projections remain structurally separate in the
     released artifact and fixtures.
3. Source-finding blur: `resolved`.
   - every projected item traces back to one exact released source finding identity and
     source packet anchor.
4. Registry / report bypass: `resolved`.
   - the lane consumes released `V39-B` and `V39-C` fixtures directly and does not
     synthesize planning from raw subjects or repo-wide scans.
5. Safe-autofix overclaim: `resolved`.
   - safe-autofix planning remains limited to findings already surfaced as released
     `safe_autofix_candidates` by `V39-C`.
6. No-op suppression: `resolved`.
   - released fixtures cover both an accepted no-op fix plan and a rejected fake no-op
     attempt for a plannable report.
7. Score / priority creep: `resolved`.
   - the fix plan remains anti-score by construction with no hidden scalar or
     merge-worthiness field.
8. Policy reinvention: `resolved`.
   - projected role guidance remains derived from released policy only and rejects
     contradictory role text.
9. Oracle-lane leakage: `resolved`.
   - `resolution_route` remains descriptive metadata only; no hybrid adjudication is
     implied or shipped in v75.
10. Authorship regression: `resolved`.
    - the released schema/model/fixture/test set governs pressure-mismatch drift only
      and does not reintroduce authorship or “AI-ness” rhetoric.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_fix_plan.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/__init__.py`
  - `packages/adeu_core_ir/schema/synthetic_pressure_mismatch_fix_plan.v1.json`
  - `spec/synthetic_pressure_mismatch_fix_plan.schema.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus75/synthetic_pressure_mismatch_fix_plan_v75_reference.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus75/synthetic_pressure_mismatch_fix_plan_v75_no_op.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus75/synthetic_pressure_mismatch_fix_plan_v75_invalid_unauthorized_route.json`
- merged guard files:
  - `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_fix_plan.py`
  - `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py`
- v75 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v39d_synthetic_pressure_mismatch_fix_plan_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v75/runtime/evidence/codex/copilot/v75-closeout-main-1/`
- review-driven hardening now includes:
  - rejection of fake no-op plans for plannable source reports,
  - semantically validated `projected_item_id` derivation and stale-id rejection,
  - strict route/posture validation for safe-autofix candidate projections,
  - strict projected-text equality against released role-policy projections.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v75_edge_closeout_summary@1",
  "arc": "vNext+75",
  "target_path": "V39-D",
  "prelock_edge_count": 10,
  "resolved_edge_count": 10,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v74": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v75)

1. The released lane remains intentionally bounded to advisory fix-plan projection and
   not actual patch generation or mutation.
2. The released lane inherits the bounded subject and detector coverage of `V39-C`; it
   does not widen that coverage by itself.
3. The closeout runtime evidence remains continuity-only provenance because v75 does
   not widen the runtime lane itself.
4. Hybrid checkpoint classification, oracle request/resolution, and adjudication remain
   deferred by design to `V39-E`.

## Recommendation (Post Closeout)

1. Mark the v75 edge set as closed with no blocking issues.
2. Treat canonical `synthetic_pressure_mismatch_fix_plan@1` plus its exported schemas
   and v75 reference/no-op/invalid-route fixtures as the released `V39-D` substrate
   going forward.
3. Keep the fix-plan lane explicitly advisory-only, anti-authorship, candidate-only for
   safe-autofix, and anti-score until a later lock widens it.
4. Keep patch generation, repo mutation, detector reruns, and hybrid oracle execution
   deferred unless they are released under new lock text.
