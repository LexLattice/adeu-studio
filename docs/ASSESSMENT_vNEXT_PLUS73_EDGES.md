# Assessment vNext+73 Edges (Post Closeout)

This document records edge disposition for `vNext+73` (`V39-B` synthetic
pressure-mismatch registry baseline) after arc closeout.

Status: post-closeout assessment (March 21, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS73_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v73_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V39-B` pressure-mismatch taxonomy and canonical registry
  baseline; canonical `synthetic_pressure_mismatch_rule_registry@1`; authoritative and
  mirrored schema exports; one deterministic v73 reference fixture; registry-local
  vocabulary; structured `counterexample_policy`; schema-level and model-level
  `safe_autofix` guard law; and closeout evidence/guard coverage.
- Out of scope: observation packets, detector rollout, conformance reports, fix plans,
  oracle request/resolution artifacts, runtime checkpoint adjudication, merge-worthiness
  scoring, authorship classification, and any broader hybrid execution widening.

## Inputs

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v13.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`
- `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch.py`
- `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch.py`
- `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_registry.py`
- `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py`
- `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/`
- `artifacts/quality_dashboard_v73_closeout.json`
- `artifacts/stop_gate/metrics_v73_closeout.json`
- `artifacts/agent_harness/v73/evidence_inputs/metric_key_continuity_assertion_v73.json`
- `artifacts/agent_harness/v73/evidence_inputs/runtime_observability_comparison_v73.json`
- `artifacts/agent_harness/v73/evidence_inputs/v39b_synthetic_pressure_mismatch_registry_evidence_v73.json`
- merged PR: `#295`

## Pre-Lock Edge Set Outcome (v73 Closeout)

1. Authorship regression: `resolved`.
   - the released schema/model/fixture govern pressure-mismatch drift only and reject
     authorship as a signal dimension.
2. Detector smuggling: `resolved`.
   - `V39-B` closes on schema law, exports, fixture, and validator coverage only; no
     observation packet, detector, report, or fix-plan surface shipped.
3. Scoring creep: `resolved`.
   - the registry remains anti-score by construction with no posture scalar or
     merge-worthiness field.
4. Weak-signal overreach: `resolved`.
   - shape-regularity remains advisory in the first slice and is explicitly blocked
     from `safe_autofix`.
5. Glossary boundary blur: `resolved`.
   - the released vocabulary remains registry-local and does not mutate the `V36-A`
     same-context glossary.
6. Package fragmentation: `resolved`.
   - first implementation placement remains entirely inside `adeu_core_ir`.
7. Oracle-lane leakage: `resolved`.
   - `resolution_route` remains metadata only; no runtime adjudication surface is
     implied or shipped in v73.
8. Utility vocabulary mush: `resolved`.
   - `expected_utility_gain` remains a bounded vocabulary in the canonical schema.
9. Registry/instance collapse: `resolved`.
   - the root artifact stays registry-only and uses bounded applicability arrays
     rather than concrete subject references.
10. Safe-autofix drift: `resolved`.
    - every `safe_autofix` rule now requires deterministic-local evidence and
      deterministic-only routing at both runtime-validator and exported-schema level.
11. Counterexample mush: `resolved`.
    - `counterexample_policy` remains required and structured with explicit
      non-application, defeating evidence, and exemption-review posture fields.
12. Registry integrity drift: `resolved`.
    - empty registries, duplicate ids, and empty applicability surfaces are rejected
      deterministically; schema exports now also carry `minItems` on the relevant
      arrays.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/__init__.py`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/synthetic_pressure_mismatch_rule_registry_v73_reference.json`
- merged guard files:
  - `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch.py`
  - `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_registry.py`
  - `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py`
- v73 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v39b_synthetic_pressure_mismatch_registry_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v73/runtime/evidence/codex/copilot/v73-closeout-main-1/`
- review-driven hardening now includes:
  - schema-level `minItems` on `rules`, `applicable_subject_kinds`, and
    `expected_utility_gains`,
  - schema-level `safe_autofix` cross-field constraints for schema-only validator
    consumers,
  - schema replay tests that verify the exported `.v1.json` rejects those invalid
    shapes directly,
  - repo-root fixture resolution in the local guard test instead of fixed parent-depth
    assumptions.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v73_edge_closeout_summary@1",
  "arc": "vNext+73",
  "target_path": "V39-B",
  "prelock_edge_count": 12,
  "resolved_edge_count": 12,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v72": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v73)

1. The released lane remains intentionally bounded to registry law rather than
   detector or fix-plan execution.
2. Schema-level constraints now cover the first-slice hard law, but broader semantic
   judgment remains intentionally deferred to later V39 slices.
3. The closeout runtime evidence is continuity-only provenance because v73 does not
   widen the runtime lane itself.
4. Future observation, projection, and hybrid adjudication widening remains deferred by
   design to `V39-C`, `V39-D`, and `V39-E`.

## Recommendation (Post Closeout)

1. Mark the v73 edge set as closed with no blocking issues.
2. Treat canonical `synthetic_pressure_mismatch_rule_registry@1` plus its exported
   schemas and v73 reference fixture as the released `V39-B` substrate going forward.
3. Keep the pressure-mismatch lane explicitly anti-authorship, anti-score, and
   registry-local in vocabulary until a later lock widens it.
4. Keep detector rollout, conformance reports, fix plans, and hybrid execution
   deferred unless they are released under new lock text.
