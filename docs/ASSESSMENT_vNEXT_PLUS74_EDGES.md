# Assessment vNext+74 Edges (Post Closeout)

This document records edge disposition for `vNext+74` (`V39-C` synthetic
pressure-mismatch observation and conformance baseline) after arc closeout.

Status: post-closeout assessment (March 22, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS74_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v74_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V39-C` pressure-mismatch observation and conformance baseline;
  canonical `synthetic_pressure_mismatch_observation_packet@1`; canonical
  `synthetic_pressure_mismatch_conformance_report@1`; authoritative and mirrored
  schema exports; committed local subject fixtures; positive and no-finding
  observation/report fixtures; rejected unsupported-execution request fixture;
  deterministic-local detector execution only; count-based and list-based report
  aggregation; and closeout evidence/guard coverage.
- Out of scope: fix plans, automatic repo mutation, hybrid oracle
  request/resolution/checkpoint artifacts, repo-wide scanning, workflow-blocking
  policy automation, authorship classification, merge-worthiness scoring, and any
  broader `V39-D` or `V39-E` widening.

## Inputs

- `docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v14.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md`
- `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_observation.py`
- `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
- `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_observation.py`
- `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py`
- `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/`
- `artifacts/quality_dashboard_v74_closeout.json`
- `artifacts/stop_gate/metrics_v74_closeout.json`
- `artifacts/agent_harness/v74/evidence_inputs/metric_key_continuity_assertion_v74.json`
- `artifacts/agent_harness/v74/evidence_inputs/runtime_observability_comparison_v74.json`
- `artifacts/agent_harness/v74/evidence_inputs/v39c_synthetic_pressure_mismatch_observation_evidence_v74.json`
- merged PR: `#296`

## Pre-Lock Edge Set Outcome (v74 Closeout)

1. Registry bypass: `resolved`.
   - released packet/report artifacts bind back to `V39-B` rule ids and reject
     carried-through metadata drift from the released registry law.
2. Detector overclaim: `resolved`.
   - `V39-C` closes on deterministic-local execution only and now fails closed when a
     released deterministic rule lacks actual subject-kind support in the detector.
3. Observation/report collapse: `resolved`.
   - packet fixtures remain concrete and reports aggregate only explicit packet ids,
     packet hashes, and subject refs.
4. Score creep: `resolved`.
   - the report remains anti-score by construction with no hidden scalar or
     merge-worthiness field.
5. Subject drift: `resolved`.
   - released subject inputs remain committed local fixtures and each packet remains
     single-subject.
6. Repo-wide scan leakage: `resolved`.
   - the first released lane stays fixture-driven and local-subject-only.
7. Fix-plan leakage: `resolved`.
   - `V39-C` ships observation and conformance only; no rewrite plan or mutation
     surface shipped.
8. Oracle-lane leakage: `resolved`.
   - `resolution_route` remains descriptive metadata only; no checkpoint runtime is
     implied or shipped in v74.
9. Positive-only fixture bias: `resolved`.
   - released fixtures cover positive detection, valid no-finding replay, and rejected
     unsupported execution.
10. Duplicate-finding inflation: `resolved`.
    - exact duplicate finding identity tuples are rejected while distinct local
      observation locators remain admissible.
11. Authorship regression: `resolved`.
    - the released schema/model/fixture/test set governs pressure-mismatch drift only
      and does not reintroduce authorship or “AI-ness” rhetoric.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_observation.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/export_schema.py`
  - `packages/adeu_core_ir/src/adeu_core_ir/__init__.py`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/subject_function_impossible_null_guard_v74.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/subject_function_clean_no_findings_v74.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/subject_code_span_impossible_null_guard_v74.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_observation_packet_v74_positive.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_observation_packet_v74_no_findings.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_conformance_report_v74_reference.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_conformance_report_v74_no_findings.json`
  - `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_unsupported_execution_request_v74.json`
- merged guard files:
  - `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_observation.py`
  - `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py`
- v74 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v39c_synthetic_pressure_mismatch_observation_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v74/runtime/evidence/codex/copilot/v74-closeout-main-1/`
- review-driven hardening now includes:
  - fail-closed rejection when a released deterministic-local rule is nominally
    applicable to a subject kind the detector does not actually support,
  - stable multi-packet report ids derived from the aggregated packet set,
  - report validation that rejects category refs whose `observation_packet_id` falls
    outside the declared aggregated packet set.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v74_edge_closeout_summary@1",
  "arc": "vNext+74",
  "target_path": "V39-C",
  "prelock_edge_count": 11,
  "resolved_edge_count": 11,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v73": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v74)

1. The released lane remains intentionally bounded to deterministic-local observation
   and conformance rather than fix-plan or oracle execution.
2. Subject coverage remains narrow by design in the first released detector baseline;
   broader subject-kind support must be widened under a later lock rather than assumed
   from registry applicability alone.
3. The closeout runtime evidence remains continuity-only provenance because v74 does
   not widen the runtime lane itself.
4. Future fix-plan projection and hybrid adjudication remain deferred by design to
   `V39-D` and `V39-E`.

## Recommendation (Post Closeout)

1. Mark the v74 edge set as closed with no blocking issues.
2. Treat canonical `synthetic_pressure_mismatch_observation_packet@1` and
   `synthetic_pressure_mismatch_conformance_report@1` plus their exported schemas and
   v74 reference fixtures as the released `V39-C` substrate going forward.
3. Keep the pressure-mismatch observation lane explicitly anti-authorship,
   deterministic-local-only, fixture-driven, and anti-score until a later lock widens
   it.
4. Keep fix plans, repo mutation, repo-wide scans, and hybrid oracle execution
   deferred unless they are released under new lock text.
