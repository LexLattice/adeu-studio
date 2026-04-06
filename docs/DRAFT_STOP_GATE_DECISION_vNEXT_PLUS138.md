# Draft Stop-Gate Decision (Post vNext+138)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS138.md`

Status: draft decision note (post-hoc closeout capture, April 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS138.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v138_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+138` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS138.md`.
- This note captures bounded `V46-C` perturbation and non-regression evidence only; it
  does not authorize projection-library widening, cross-subject ranking, or downstream
  consumer seams by itself.
- Canonical `V46-C` release in `v138` is carried by the shipped
  `packages/adeu_benchmarking` perturbation/non-regression package surface,
  authoritative and mirrored starter schema export, deterministic `v46c`
  fixtures/tests, and the canonical
  `v46c_procedural_depth_perturbation_evidence@1` evidence input under
  `artifacts/agent_harness/v138/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` now marks `V46-C`
  closed on `main` and advances the branch-local default next path to `V46-D`; it
  does not by itself authorize `V46-D` implementation.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#360` (`feat(v138): add procedural depth perturbation bundle`)
- arc-completion merge commit: `a782dfdcadc264a8b879750374b8039436db7b45`
- merged-at timestamp: `2026-04-06T01:49:53Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v138_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v138_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v138_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v138/evidence_inputs/metric_key_continuity_assertion_v138.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v138/evidence_inputs/runtime_observability_comparison_v138.json`
  - `V46-C` release evidence input:
    `artifacts/agent_harness/v138/evidence_inputs/v46c_procedural_depth_perturbation_evidence_v138.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS138_EDGES.md`

## Exit-Criteria Check (vNext+138)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V46-C` merged with green CI | required | `pass` | PR `#360`, merge commit `a782dfdcadc264a8b879750374b8039436db7b45`, checks `python/web/lean-formal = pass` |
| `packages/adeu_benchmarking` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_benchmarking` only |
| Four starter perturbation/non-regression contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_procedural_depth_perturbation_case@1`, `adeu_procedural_depth_failure_topology@1`, `adeu_procedural_depth_non_regression_report@1`, and `adeu_procedural_depth_benchmark_validation_report@1` |
| Released `V46-A` substrate and released `V46-B` baseline stack are consumed without reopening doctrine or forking baseline schema ids | required | `pass` | shipped `V46-C` contracts bind to the released family/projection/execution-context substrate and reuse released instance/gold/run/metrics/diagnostic contracts directly |
| Starter perturbation cases remain operational and materializable rather than label-only shells | required | `pass` | released perturbation-case fixtures carry ordered `perturbation_overlay_events`, bounded optional paraphrase summary override, and materialize deterministic repeated run traces |
| Starter perturbation bundle remains one small deterministic bundle over the released `hierarchical_3x3` baseline only | required | `pass` | committed `v46c` fixtures stay bounded to `branch_shift`, `delayed_constraint`, and `paraphrase_preserving` over the released baseline instance only |
| Exact starter non-regression thresholds are enforced over the frozen replay subjects | required | `pass` | released non-regression helper/report use exact-match replay stability over run-trace id, metrics id, diagnostic-report id, dominant family, and terminal status across replay count `3` |
| Aggregation artifacts carry explicit per-case and per-replay structure rather than parallel top-level arrays | required | `pass` | released failure topology, non-regression, and benchmark validation artifacts carry per-case bundles with explicit replay-indexed refs |
| Unknown replay override case refs fail closed instead of being silently dropped | required | `pass` | review hardening commit `85c02d2bc348a1a96066e24c209a147ee6e4fc26` rejects unknown override keys in `evaluate_procedural_depth_perturbation_bundle(...)` |
| Top-level validation aggregation requires expected/observed agreement in addition to replay stability | required | `pass` | review hardening commit `85c02d2bc348a1a96066e24c209a147ee6e4fc26` tightened `deterministic_replay_confirmed` so deterministic but wrong expectations do not surface as top-level validation success |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v138_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v138/evidence_inputs/metric_key_continuity_assertion_v138.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v138/evidence_inputs/runtime_observability_comparison_v138.json` |

## Stop-Gate Summary

```json
{
  "schema": "v138_closeout_stop_gate_summary@1",
  "arc": "vNext+138",
  "target_path": "V46-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v137": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v137_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v138_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+137","current_arc":"vNext+138","baseline_source":"artifacts/stop_gate/report_v137_closeout.md","current_source":"artifacts/stop_gate/report_v138_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":134,"delta_ms":0,"notes":"v138 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V46-C Procedural Depth perturbation and non-regression lane: one repo-owned adeu_benchmarking package only, four new bounded V46-C contracts over the released V46-A/V46-B stack, operational perturbation overlays for branch_shift delayed_constraint and paraphrase_preserving, exact three-replay deterministic non-regression thresholds, per-case and per-replay aggregation across failure topology non-regression and benchmark validation artifacts, schema mirrors and deterministic v46c fixtures, fail-closed unknown override-case handling, validation aggregation that now requires expected/observed agreement in addition to replay stability, and no cross-subject comparison or downstream consumer widening."}
```

## V46C Perturbation And Non-Regression Evidence

```json
{"schema":"v46c_procedural_depth_perturbation_evidence@1","evidence_input_path":"artifacts/agent_harness/v138/evidence_inputs/v46c_procedural_depth_perturbation_evidence_v138.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS138.md#v138-continuation-contract-machine-checkable","merged_pr":"#360","merge_commit":"a782dfdcadc264a8b879750374b8039436db7b45","implementation_commit":"bafac3712d401c81910e16dd364f3024ab6b972a","review_hardening_commit":"85c02d2bc348a1a96066e24c209a147ee6e4fc26","implementation_packages":["adeu_benchmarking"],"starter_schema_ids":["adeu_procedural_depth_perturbation_case@1","adeu_procedural_depth_failure_topology@1","adeu_procedural_depth_non_regression_report@1","adeu_procedural_depth_benchmark_validation_report@1"],"starter_perturbation_kind_vocabulary":["branch_shift","delayed_constraint","paraphrase_preserving"],"reused_v46b_dominant_failure_family_vocabulary":["clean_success","horizontal_plan_spine","vertical_active_step_compilation","reintegration","mixed"],"reused_v46b_terminal_trace_status_vocabulary":["completed_clean","completed_with_structural_break"],"starter_replay_count":3,"evaluation_context_posture":"deterministic_fixed_context","per_case_per_replay_aggregation_required":true,"unknown_override_case_refs_fail_closed":true,"top_level_validation_requires_expected_observed_agreement":true,"test_reference_path":"packages/adeu_benchmarking/tests/test_benchmarking_procedural_depth_perturbation.py","metric_key_continuity_assertion_path":"artifacts/agent_harness/v138/evidence_inputs/metric_key_continuity_assertion_v138.json","runtime_observability_comparison_path":"artifacts/agent_harness/v138/evidence_inputs/runtime_observability_comparison_v138.json","notes":"v138 evidence pins the released V46-C perturbation and non-regression seam on main: one repo-owned adeu_benchmarking package only, four new bounded contracts over the released V46-A/V46-B stack, one tiny deterministic perturbation bundle over hierarchical_3x3, exact three-replay deterministic non-regression thresholds, deterministic schema mirrors and v46c fixtures, and no cross-subject comparison or downstream consumer widening."}
```

## Recommendation (Post v138)

- gate decision:
  - `V46C_PERTURBATION_AND_NON_REGRESSION_COMPLETE_ON_MAIN`
- rationale:
  - `v138` closes the first perturbation and repeated-run widening seam on `main`
    after the benchmark substrate (`V46-A`) and the baseline procedural-depth
    projection (`V46-B`) were already released.
  - the shipped slice stayed narrow and replay-first:
    - one repo-owned package
    - four released perturbation/non-regression contracts only
    - one tiny deterministic perturbation bundle over the released
      `hierarchical_3x3` baseline only
    - exact three-replay deterministic thresholds only
    - per-case and per-replay aggregation only
    - no cross-subject comparison
    - no projection-library widening
    - no downstream consumer seam
  - review hardening stayed bounded and materially improved repo alignment:
    `85c02d2bc348a1a96066e24c209a147ee6e4fc26` now rejects unknown override-case refs
    and prevents deterministically wrong expectations from surfacing as top-level
    validation success.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat at `0 ms` delta versus the `v137` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` should now be read with `V46-C` closed on
    `main` and `V46-D` selected as the next branch-local default path.
