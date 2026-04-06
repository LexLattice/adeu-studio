# Draft Stop-Gate Decision (Post vNext+139)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS139.md`

Status: draft decision note (post-hoc closeout capture, April 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS139.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v139_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+139` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS139.md`.
- This note captures bounded `V46-D` cross-subject comparison evidence only; it does
  not authorize projection-library widening, ranking doctrine, or downstream consumer
  seams by itself.
- Canonical `V46-D` release in `v139` is carried by the shipped
  `packages/adeu_benchmarking` comparison package surface, authoritative and mirrored
  starter schema export, deterministic `v46d` fixtures/tests, and the canonical
  `v46d_cross_subject_comparison_evidence@1` evidence input under
  `artifacts/agent_harness/v139/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` now marks `V46-D`
  closed on `main` and advances the branch-local default next path to `V46-E`; it
  does not by itself authorize `V46-E` implementation.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#361` (`feat(v139): add cross-subject benchmark comparison`)
- arc-completion merge commit: `c898bf9da452a7b2c8ba8811e81c98ad261c6674`
- merged-at timestamp: `2026-04-06T10:16:16Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v139_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v139_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v139_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v139/evidence_inputs/metric_key_continuity_assertion_v139.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v139/evidence_inputs/runtime_observability_comparison_v139.json`
  - `V46-D` release evidence input:
    `artifacts/agent_harness/v139/evidence_inputs/v46d_cross_subject_comparison_evidence_v139.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS139_EDGES.md`

## Exit-Criteria Check (vNext+139)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V46-D` merged with green CI | required | `pass` | PR `#361`, merge commit `c898bf9da452a7b2c8ba8811e81c98ad261c6674`, checks `python/web/lean-formal = pass` |
| `packages/adeu_benchmarking` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_benchmarking` only |
| Four starter cross-subject comparison contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_benchmark_subject_record@1`, `adeu_cross_subject_comparison_case@1`, `adeu_cross_subject_comparison_report@1`, and `adeu_cross_subject_comparison_validation_report@1` |
| Released `V46-A`, `V46-B`, and `V46-C` artifacts are consumed without reopening scorer law or forking schema ids | required | `pass` | shipped `V46-D` subject records and comparison cases bind directly to the released family/projection/execution-context substrate and the released procedural-depth baseline and perturbation stack |
| Starter comparison stays descriptive and non-promotional | required | `pass` | released comparison reports remain bounded to `comparison_ready_clean` / `comparison_incompatible` posture with no ranking, routing, or training authority |
| Starter subject pair remains deterministic and compatibility-scoped | required | `pass` | released helper enforces one `base_model` plus one `prompted_model`, deterministic fixed context, and exact compatibility over `repo_snapshot_ref`, `tool_availability`, `context_budget_posture`, and `determinism_posture` |
| Comparison bundle stays bound to one shared released perturbation bundle | required | `pass` | released subject records carry `perturbation_bundle_ref` and ordered `perturbation_case_refs`, and comparison evaluation fails closed if the released bundle diverges across the pair |
| Per-surface comparison law remains explicit and finite | required | `pass` | released comparison evaluation freezes `baseline_structural_fidelity`, `perturbation_non_regression`, and `perturbation_validation` as the only starter surfaces and materializes explicit `exact_match` / `different_but_comparable` / `insufficient_evidence` outcomes |
| Review hardening preserves subject/context and baseline artifact-chain integrity | required | `pass` | review hardening commit `a4c7ea0211900d134febc48764f43d06b216f22e` now enforces subject-class versus execution-context consistency and baseline metric/diagnostic chain validation on both sides |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v139_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v139/evidence_inputs/metric_key_continuity_assertion_v139.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v139/evidence_inputs/runtime_observability_comparison_v139.json` |

## Stop-Gate Summary

```json
{
  "schema": "v139_closeout_stop_gate_summary@1",
  "arc": "vNext+139",
  "target_path": "V46-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v138": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v138_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v139_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+138","current_arc":"vNext+139","baseline_source":"artifacts/stop_gate/report_v138_closeout.md","current_source":"artifacts/stop_gate/report_v139_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":134,"delta_ms":0,"notes":"v139 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V46-D cross-subject comparison lane: one repo-owned adeu_benchmarking package only, four new bounded comparison contracts over the released V46-A/V46-B/V46-C procedural-depth stack, one deterministic base_model versus prompted_model subject pair, explicit execution-context compatibility law rather than shared-context identity, per-surface comparison over baseline structural fidelity perturbation non-regression and perturbation validation only, review hardening for subject-class/context binding and baseline metric/diagnostic chain integrity, deterministic schema mirrors and v46d fixtures, and no ranking or downstream consumer widening."}
```

## V46D Cross-Subject Comparison Evidence

```json
{"schema":"v46d_cross_subject_comparison_evidence@1","evidence_input_path":"artifacts/agent_harness/v139/evidence_inputs/v46d_cross_subject_comparison_evidence_v139.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS139.md#v139-continuation-contract-machine-checkable","merged_pr":"#361","merge_commit":"c898bf9da452a7b2c8ba8811e81c98ad261c6674","implementation_commit":"c88a927dfff6f06fd20b903bc0852aaf066fe9c5","review_hardening_commit":"a4c7ea0211900d134febc48764f43d06b216f22e","implementation_packages":["adeu_benchmarking"],"starter_schema_ids":["adeu_benchmark_subject_record@1","adeu_cross_subject_comparison_case@1","adeu_cross_subject_comparison_report@1","adeu_cross_subject_comparison_validation_report@1"],"starter_subject_pair":["base_model","prompted_model"],"required_execution_context_compatibility_fields":["repo_snapshot_ref","tool_availability","context_budget_posture","determinism_posture"],"required_comparison_surfaces":["baseline_structural_fidelity","perturbation_non_regression","perturbation_validation"],"test_reference_path":"packages/adeu_benchmarking/tests/test_benchmarking_cross_subject_comparison.py","metric_key_continuity_assertion_path":"artifacts/agent_harness/v139/evidence_inputs/metric_key_continuity_assertion_v139.json","runtime_observability_comparison_path":"artifacts/agent_harness/v139/evidence_inputs/runtime_observability_comparison_v139.json","notes":"v139 evidence pins the released V46-D cross-subject comparison seam on main: one repo-owned adeu_benchmarking package only, four new bounded comparison contracts over the released V46-A/V46-B/V46-C procedural-depth stack, one deterministic base_model versus prompted_model subject pair, descriptive comparison-only posture, explicit perturbation-bundle sameness and compatibility law, fail-closed subject-class/context and baseline artifact-chain validation, deterministic schema mirrors and v46d fixtures, and no ranking or downstream consumer widening."}
```

## Recommendation (Post v139)

- gate decision:
  - `V46D_CROSS_SUBJECT_COMPARISON_COMPLETE_ON_MAIN`
- rationale:
  - `v139` closes the first cross-subject comparison seam on `main` after the
    benchmark substrate (`V46-A`), the baseline procedural-depth projection (`V46-B`),
    and the perturbation/non-regression lane (`V46-C`) were already released.
  - the shipped slice stayed narrow and comparison-first:
    - one repo-owned package
    - four released comparison contracts only
    - one deterministic `base_model` versus `prompted_model` subject pair only
    - exact compatibility over released execution-context fields only
    - same released baseline instance and perturbation bundle only
    - descriptive cross-subject comparison only
    - no ranking
    - no projection-library widening
    - no downstream consumer seam
  - review hardening stayed bounded and materially improved repo alignment:
    `a4c7ea0211900d134febc48764f43d06b216f22e` now rejects subject/context class
    drift and mixed baseline metric/diagnostic chains before comparison artifacts are
    emitted.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat at `0 ms` delta versus the `v138` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` should now be read with `V46-D` closed on
    `main` and `V46-E` selected as the next branch-local default path.
