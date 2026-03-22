# Draft Stop-Gate Decision (Post vNext+75)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md`

Status: draft decision note (post-hoc closeout capture, March 22, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS75.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v75_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+75` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md`.
- This note captures `V39-D` synthetic pressure-mismatch fix-plan and policy-projection
  closeout evidence only; it does not authorize patch generation, repo mutation,
  hybrid oracle execution, new detector rollout, or any broader repo-wide scanning
  surface by itself.
- Canonical `V39-D` release in v75 is carried by canonical
  `synthetic_pressure_mismatch_fix_plan@1`, authoritative and mirrored schema exports
  under `packages/adeu_core_ir/schema/` and `spec/`, committed v75 fix-plan fixtures,
  and canonical `v39d_synthetic_pressure_mismatch_fix_plan_evidence@1`.
- The released v75 lane remains intentionally bounded:
  it consumes the released `V39-B` registry and `V39-C` conformance lane rather than
  redefining them, keeps forward-agent and post-optimizer projections structurally
  separate, preserves exact source-finding traceability, keeps `safe_autofix`
  candidate-only, keeps all outputs advisory-only, preserves anti-authorship and
  anti-score posture, and treats `resolution_route` as carried-through metadata rather
  than proof that `V39-E` adjudication exists.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `b6b10d0a8158c3289d38ae4768666bf54a18bdbc`
- arc-completion CI runs:
  - PR `#297`
    - head commit: `a753737fe452630db886d16965697f62d33f0804`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23399071291`
    - conclusion: `success`
  - branch push before merge
    - head commit: `a753737fe452630db886d16965697f62d33f0804`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23399070630`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `b6b10d0a8158c3289d38ae4768666bf54a18bdbc`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23399357490`
    - conclusion: `success`
- merged implementation PRs:
  - `#297` (`Implement V39-D fix plan projection baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v75_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v75_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v75_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v75/evidence_inputs/metric_key_continuity_assertion_v75.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v75/evidence_inputs/runtime_observability_comparison_v75.json`
  - V39-D fix-plan evidence input:
    `artifacts/agent_harness/v75/evidence_inputs/v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v75/runtime/evidence/codex/copilot/v75-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v75/runtime/evidence/codex/copilot/v75-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v75 remains carried by the typed
    fix-plan/schema/fixture artifacts plus the closeout quality and stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS75_EDGES.md`

## Exit-Criteria Check (vNext+75)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V39-D` merged with green CI | required | `pass` | PR `#297`, merge commit `b6b10d0a8158c3289d38ae4768666bf54a18bdbc`, Actions runs `23399071291` and `23399357490` |
| Canonical `synthetic_pressure_mismatch_fix_plan@1` validates and exports cleanly | required | `pass` | `packages/adeu_core_ir/schema/synthetic_pressure_mismatch_fix_plan.v1.json`, `spec/synthetic_pressure_mismatch_fix_plan.schema.json`, and `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_fix_plan.py` |
| Fix plans consume released `V39-C` conformance reports rather than bypassing them through raw subjects | required | `pass` | `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_fix_plan.py`, `derive_v39d_fix_plan()`, and the released v74 report fixtures consumed by the v75 reference fixtures |
| Forward-agent and post-optimizer policy projection remain structurally separate | required | `pass` | `synthetic_pressure_mismatch_fix_plan_v75_reference.json` and `test_v39d_reference_fix_plan_fixture_validates_and_replays` |
| Projected plan items bind exact released source findings rather than loose finding-shaped areas | required | `pass` | reference/no-op fixtures and `v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json` |
| Safe-autofix planning remains candidate-only and never becomes executable payload or edit instruction | required | `pass` | reference fixture, `test_v39d_invalid_unauthorized_route_fixture_fails_closed`, and `v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json` |
| Plannable released findings must surface in at least one projected plan item | required | `pass` | `test_v39d_fix_plan_rejects_no_op_for_plannable_report` and `v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json` |
| `projected_item_id` must match validated projection semantics | required | `pass` | `test_v39d_fix_plan_rejects_stale_projected_item_id` and `v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json` |
| Projected text may not deviate from released role policy projections | required | `pass` | `test_v39d_fix_plan_rejects_text_that_deviates_from_released_role_policy` and `test_v39d_derived_projection_text_tracks_released_role_policy` |
| Valid no-op fix plans replay for no-finding source reports | required | `pass` | `synthetic_pressure_mismatch_fix_plan_v75_no_op.json` and `test_v39d_no_op_fix_plan_fixture_validates_and_replays` |
| Invalid planning routes fail closed | required | `pass` | `synthetic_pressure_mismatch_fix_plan_v75_invalid_unauthorized_route.json` and `test_v39d_invalid_unauthorized_route_fixture_fails_closed` |
| Anti-authorship and anti-score boundaries remain preserved | required | `pass` | `test_v39d_fix_plan_rejects_authorship_signal_kind`, `test_v39d_fix_plan_rejects_hidden_score_field`, and `v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v75_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v75/evidence_inputs/metric_key_continuity_assertion_v75.json` records exact keyset equality versus v74 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v75/evidence_inputs/runtime_observability_comparison_v75.json` |

## Stop-Gate Summary

```json
{
  "schema": "v75_closeout_stop_gate_summary@1",
  "arc": "vNext+75",
  "target_path": "V39-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v74": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 101,
  "runtime_observability_delta_ms": 5
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v74_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v75_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+74","baseline_elapsed_ms":96,"baseline_source":"artifacts/stop_gate/report_v74_closeout.md","current_arc":"vNext+75","current_elapsed_ms":101,"current_source":"artifacts/stop_gate/report_v75_closeout.md","delta_ms":5,"notes":"v75 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V39-D synthetic pressure-mismatch fix-plan projection lane.","schema":"runtime_observability_comparison@1"}
```

## V39D Synthetic Pressure-Mismatch Fix-Plan Evidence

```json
{
  "anti_authorship_boundary_preserved": true,
  "anti_score_boundary_preserved": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md#v39d_synthetic_pressure_mismatch_fix_plan_contract@1",
  "evidence_input_path": "artifacts/agent_harness/v75/evidence_inputs/v39d_synthetic_pressure_mismatch_fix_plan_evidence_v75.json",
  "evaluator_id": "adeu_core_ir.synthetic_pressure_mismatch_fix_plan.derive_v39d_fix_plan@1",
  "evaluator_version": "1",
  "implementation_source_hash": "c0d8e18d7eae4a42d5a40b96e71cc27306cc2f77ee32587c63d290406271fcbb",
  "implementation_source_path": "packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_fix_plan.py",
  "notes": "v75 evidence pins the released fix-plan schema, accepted and no-op fixtures, invalid-route fail-closed coverage, and the bounded V39-D advisory / anti-authorship / anti-score contract on main.",
  "policy_sources": [
    {
      "path": "AGENTS.md",
      "sha256": "4ee9bbb70d02036e72deaaba7348a3b7e8d93b0a7431535a4597be08b7af7f93"
    },
    {
      "path": "docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md",
      "sha256": "63d36a286e0a6fa027209e7fc77377593deef80b71bf50fe495a25d8bcca55c5"
    },
    {
      "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS75.md",
      "sha256": "050639636283ab7262370b7e93d63e8b4ac569ecba8c777f905754c791756d54"
    }
  ],
  "schema": "v39d_synthetic_pressure_mismatch_fix_plan_evidence@1",
  "schema_export_parity_verified": true,
  "source_finding_binding_exact_verified": true,
  "verification_passed": true
}
```

## Recommendation (Post v75)

- gate decision:
  - `V39D_SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_COMPLETE_ON_MAIN`
- rationale:
  - v75 closes the bounded `V39-D` baseline with canonical
    `synthetic_pressure_mismatch_fix_plan@1`, authoritative/mirrored schema exports,
    committed v75 reference/no-op/invalid-route fixtures, and canonical
    `v39d_synthetic_pressure_mismatch_fix_plan_evidence@1` integrated on `main`.
  - the released lane remains explicitly bounded to advisory plan projection only; it
    does not widen into patch generation, file-edit payloads, repo mutation, detector
    reruns, or hybrid adjudication.
  - review-driven hardening on the merged PR now preserves exact source-finding
    surfacing for plannable findings, semantically validated `projected_item_id`
    binding, and strict role-policy-projection text equality.
  - no stop-gate schema-family, metric-key, or runtime-observability regressions were
    introduced by the lane.
