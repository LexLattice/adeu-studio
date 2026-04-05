# Draft Stop-Gate Decision (Post vNext+136)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS136.md`

Status: draft decision note (post-hoc closeout capture, April 5, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS136.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v136_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+136` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS136.md`.
- This note captures bounded `V46-A` benchmark-substrate evidence only; it does not
  authorize procedural-depth benchmark scoring, rankings, perturbation widening, or
  downstream consumer seams by itself.
- Canonical `V46-A` release in `v136` is carried by the shipped
  `packages/adeu_benchmarking` substrate package, authoritative and mirrored starter
  schema export, deterministic `v46a` fixtures/tests, and the canonical
  `v46a_benchmark_substrate_evidence@1` evidence input under
  `artifacts/agent_harness/v136/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` now marks `V46-A`
  closed on `main` and advances the branch-local default next path to `V46-B`; it does
  not by itself authorize `V46-B` implementation.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#358` (`feat(v136): add benchmark substrate contracts`)
- arc-completion merge commit: `3a1d052b01a0438b41cab7e6be87c7cbebcf02d1`
- merged-at timestamp: `2026-04-05T23:07:38Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v136_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v136_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v136_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v136/evidence_inputs/metric_key_continuity_assertion_v136.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v136/evidence_inputs/runtime_observability_comparison_v136.json`
  - `V46-A` release evidence input:
    `artifacts/agent_harness/v136/evidence_inputs/v46a_benchmark_substrate_evidence_v136.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS136_EDGES.md`

## Exit-Criteria Check (vNext+136)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V46-A` merged with green CI | required | `pass` | PR `#358`, merge commit `3a1d052b01a0438b41cab7e6be87c7cbebcf02d1`, checks `python/web/lean-formal = pass` |
| `packages/adeu_benchmarking` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_benchmarking` only |
| Four starter benchmark contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_benchmark_family_spec@1`, `adeu_benchmark_projection_spec@1`, `adeu_benchmark_execution_context@1`, and `adeu_benchmark_validation_report@1` |
| Released `V44` doctrine constrains but is not redefined or ingested as runtime payload authority | required | `pass` | released family/projection specs cite `V44` doctrine and `V44` schema ids as constraint sources only |
| Projection specs declare downstream procedural-depth contract ids without claiming those artifacts already ship | required | `pass` | released projection fixture/spec names `adeu_procedural_depth_*@1` ids as declaration-only starter fields |
| Reliability and non-regression summaries remain policy-declarative only | required | `pass` | shipped family-spec fields remain substrate policy summaries only, with no empirical reliability artifact claims |
| Execution contexts require explicit subject identity, determinism posture, context-budget posture, and repo snapshot identity | required | `pass` | released `adeu_benchmark_execution_context@1` fixture/schema/helper surface enforces those fields deterministically |
| Validation reports remain deterministic, fixture-scoped, and non-promotional | required | `pass` | shipped validation-report helper and `v46a` matrix keep `case_ref` fixture-scoped and benchmark outputs diagnostic-only |
| Positive validation-case coverage exists for the full starter dominant-family vocabulary | required | `pass` | committed `reference_v46a_validation_case_matrix.json` and `reference_benchmark_validation_report.json` exercise `clean_success`, `horizontal_plan_spine`, `vertical_active_step_compilation`, `reintegration`, and `mixed` |
| Composite human-plus-tool-plus-model subject posture remains deferred from the starter taxonomy | required | `pass` | released `subject_under_test_classes` vocabulary remains bounded to the five starter classes only |
| Review hardening resolved `schema` shadowing and canonical-helper drift without widening semantics | required | `pass` | review hardening commit `1e994dfb7ba93bfcaba4f5107a2752de2e787c6b` switched to alias-backed `schema_id`, reused `urm_runtime.hashing`, and preserved starter behavior |
| Full Python lane passed after review hardening | required | `pass` | local `make check` passed before merge-update push, and final CI `python` check passed on the hardening commit |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v136_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v136/evidence_inputs/metric_key_continuity_assertion_v136.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v136/evidence_inputs/runtime_observability_comparison_v136.json` |

## Stop-Gate Summary

```json
{
  "schema": "v136_closeout_stop_gate_summary@1",
  "arc": "vNext+136",
  "target_path": "V46-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v135": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v135_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v136_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+135","current_arc":"vNext+136","baseline_source":"artifacts/stop_gate/report_v135_closeout.md","current_source":"artifacts/stop_gate/report_v136_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":134,"delta_ms":0,"notes":"v136 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V46-A benchmark-substrate lane: one repo-owned adeu_benchmarking package only, four released starter contracts for family spec, projection spec, execution context, and validation report, explicit benchmark-output epistemic posture and diagnostic-only non-promotional interpretation, declaration-only downstream procedural-depth contract ids, deterministic fixture-scoped validation with positive mixed coverage, explicit starter subject-under-test taxonomy with composite human-plus-tool-plus-model posture deferred, and review hardening that replaced BaseModel.schema shadowing with alias-backed schema_id fields and reused the shared canonical hashing helper inventory."}
```

## V46A Benchmark Substrate Evidence

```json
{"schema":"v46a_benchmark_substrate_evidence@1","evidence_input_path":"artifacts/agent_harness/v136/evidence_inputs/v46a_benchmark_substrate_evidence_v136.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS136.md#v136-continuation-contract-machine-checkable","merged_pr":"#358","merge_commit":"3a1d052b01a0438b41cab7e6be87c7cbebcf02d1","implementation_commit":"b71a5fe467ebb7e5a909685064c69d0c7bd9a18e","review_hardening_commit":"1e994dfb7ba93bfcaba4f5107a2752de2e787c6b","implementation_packages":["adeu_benchmarking"],"benchmarking_package_root":"packages/adeu_benchmarking","benchmarking_pyproject_path":"packages/adeu_benchmarking/pyproject.toml","benchmarking_models_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/models.py","benchmarking_export_schema_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py","benchmarking_package_init_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py","benchmark_family_spec_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_benchmark_family_spec.v1.json","benchmark_projection_spec_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_benchmark_projection_spec.v1.json","benchmark_execution_context_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_benchmark_execution_context.v1.json","benchmark_validation_report_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_benchmark_validation_report.v1.json","benchmark_family_spec_mirror_schema_path":"spec/adeu_benchmark_family_spec.schema.json","benchmark_projection_spec_mirror_schema_path":"spec/adeu_benchmark_projection_spec.schema.json","benchmark_execution_context_mirror_schema_path":"spec/adeu_benchmark_execution_context.schema.json","benchmark_validation_report_mirror_schema_path":"spec/adeu_benchmark_validation_report.schema.json","reference_family_spec_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_benchmark_family_spec.json","reference_projection_spec_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_benchmark_projection_spec.json","reference_execution_context_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_benchmark_execution_context.json","reference_validation_report_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_benchmark_validation_report.json","reference_validation_case_matrix_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_v46a_validation_case_matrix.json","reject_projection_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reject_benchmark_projection_spec_missing_declared_contract_ids.json","reject_validation_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reject_benchmark_validation_report_unsupported_dominant_family.json","test_reference_path":"packages/adeu_benchmarking/tests/test_benchmarking_models.py","makefile_bootstrap_path":"Makefile","starter_schema_ids":["adeu_benchmark_family_spec@1","adeu_benchmark_projection_spec@1","adeu_benchmark_execution_context@1","adeu_benchmark_validation_report@1"],"subject_under_test_class_vocabulary":["base_model","prompted_model","routed_runtime","multi_agent_system","adeu_runtime_surface"],"dominant_failure_family_vocabulary":["clean_success","horizontal_plan_spine","vertical_active_step_compilation","reintegration","mixed"],"clean_success_non_failure_sentinel_frozen":true,"composite_human_tool_model_subject_class_deferred_from_v46a":true,"projection_declares_future_contract_ids_only":true,"reliability_and_non_regression_policy_summaries_declarative_only":true,"shared_canonical_hashing_helper_reused":true,"schema_alias_pattern_reused":true,"local_full_python_gate":"make check","metric_key_continuity_assertion_path":"artifacts/agent_harness/v136/evidence_inputs/metric_key_continuity_assertion_v136.json","runtime_observability_comparison_path":"artifacts/agent_harness/v136/evidence_inputs/runtime_observability_comparison_v136.json","runtime_event_stream_path":"artifacts/agent_harness/v136/runtime/evidence/local/urm_events.ndjson","notes":"v136 evidence pins the released V46-A benchmark-substrate seam on main: one repo-owned adeu_benchmarking package only, four released starter contracts for benchmark family spec, benchmark projection spec, benchmark execution context, and benchmark validation report, deterministic authoritative schema export plus root mirrors, deterministic v46a fixtures/tests including positive mixed coverage, declaration-only downstream procedural-depth contract ids, explicit starter subject-under-test taxonomy and benchmark-output epistemic posture, and review hardening that removed BaseModel.schema shadowing and canonical helper drift without widening benchmark semantics."}
```

## Recommendation (Post v136)

- gate decision:
  - `V46A_BENCHMARK_SUBSTRATE_COMPLETE_ON_MAIN`
- rationale:
  - `v136` closes the bounded benchmark-substrate seam on `main` before the first
    concrete procedural-depth benchmark projection is released.
  - the shipped slice stayed narrow and substrate-first:
    - one repo-owned package
    - four starter benchmark contracts only
    - explicit subject-under-test taxonomy
    - explicit benchmark-output epistemic posture
    - declaration-only downstream procedural-depth contract ids
    - deterministic fixture-scoped validation only
    - no live procedural-depth instance, run-trace, metrics, or diagnostic artifacts
  - review hardening stayed bounded and materially improved repo alignment:
    `1e994dfb7ba93bfcaba4f5107a2752de2e787c6b` replaced BaseModel-shadowing
    `schema` fields with alias-backed `schema_id` fields, reused the shared
    `urm_runtime.hashing` helpers, and restored canonical-helper inventory conformity.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat at `0 ms` delta versus the `v135` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` should now be read with `V46-A` closed on
    `main` and `V46-B` selected as the next branch-local default path.
