# Draft Stop-Gate Decision (Post vNext+137)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS137.md`

Status: draft decision note (post-hoc closeout capture, April 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS137.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v137_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+137` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS137.md`.
- This note captures bounded `V46-B` procedural-depth projection evidence only; it
  does not authorize perturbation widening, non-regression promotion, cross-subject
  comparison, or downstream consumer seams by itself.
- Canonical `V46-B` release in `v137` is carried by the shipped
  `packages/adeu_benchmarking` procedural-depth models/scorer package surface,
  authoritative and mirrored starter schema export, deterministic `v46b`
  fixtures/tests, and the canonical
  `v46b_procedural_depth_projection_evidence@1` evidence input under
  `artifacts/agent_harness/v137/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` now marks `V46-B`
  closed on `main` and advances the branch-local default next path to `V46-C`; it
  does not by itself authorize `V46-C` implementation.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#359` (`feat(v137): add procedural depth projection artifacts`)
- arc-completion merge commit: `0ac0f85297d9a73fb625b605fff7919ab1525ce4`
- merged-at timestamp: `2026-04-06T00:57:12Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v137_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v137_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v137_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v137/evidence_inputs/metric_key_continuity_assertion_v137.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v137/evidence_inputs/runtime_observability_comparison_v137.json`
  - `V46-B` release evidence input:
    `artifacts/agent_harness/v137/evidence_inputs/v46b_procedural_depth_projection_evidence_v137.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS137_EDGES.md`

## Exit-Criteria Check (vNext+137)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V46-B` merged with green CI | required | `pass` | PR `#359`, merge commit `0ac0f85297d9a73fb625b605fff7919ab1525ce4`, checks `python/web/lean-formal = pass` |
| `packages/adeu_benchmarking` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_benchmarking` only |
| Five starter procedural-depth contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_procedural_depth_instance@1`, `adeu_procedural_depth_gold_trace@1`, `adeu_procedural_depth_run_trace@1`, `adeu_procedural_depth_metrics@1`, and `adeu_procedural_depth_diagnostic_report@1` |
| Released `V46-A` substrate is consumed without reopening benchmark-substrate doctrine | required | `pass` | released `V46-A` family spec, projection spec, and execution context remain upstream refs only while `V46-B` ships the first concrete procedural-depth stack |
| Actual released procedural-depth schema ids bind exactly to the ids already declared by the released projection spec | required | `pass` | shipped `adeu_procedural_depth_*@1` ids match the `declared_*_contract_id` fields already released in the `V46-A` projection spec |
| Starter reference world remains one tiny deterministic `hierarchical_3x3` chain only | required | `pass` | released instance contract and committed `v46b` fixtures admit one bounded hierarchical `3x3` reference chain only |
| Gold trace derives deterministically from the released instance and run traces score deterministically against the bound gold trace | required | `pass` | shipped `derive_procedural_depth_gold_trace(...)`, `score_procedural_depth_run(...)`, and reference replay tests in `packages/adeu_benchmarking/tests/test_benchmarking_procedural_depth.py` |
| Gold/run event objects and supporting refs are structurally rich and trace-qualified | required | `pass` | released event payloads carry `event_index`, `step_ref`, `step_role`, bounded parent/return targeting, and support refs remain `gold/run` trace-qualified |
| Positive starter fixtures exercise the full released dominant-family vocabulary | required | `pass` | committed `reference_v46b_scoring_matrix.json` plus the degraded run-trace fixtures exercise `clean_success`, `horizontal_plan_spine`, `vertical_active_step_compilation`, `reintegration`, and `mixed` |
| Imported materialization/id-ordering bug is not carried into the live repo-owned implementation | required | `pass` | shipped instance materialization canonicalizes `step_specs` before id assignment, and the regression test replays canonical ordering before id validation |
| Review hardening resolved compute/materialize parity for procedural-depth ids without widening semantics | required | `pass` | review hardening commit `f826779966063822bf53f84d4d52c16b5da5ddb6` canonicalized exported procedural-depth `compute_*_id` helpers to match materialization/validation behavior |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v137_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v137/evidence_inputs/metric_key_continuity_assertion_v137.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v137/evidence_inputs/runtime_observability_comparison_v137.json` |

## Stop-Gate Summary

```json
{
  "schema": "v137_closeout_stop_gate_summary@1",
  "arc": "vNext+137",
  "target_path": "V46-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v136": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v136_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v137_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+136","current_arc":"vNext+137","baseline_source":"artifacts/stop_gate/report_v136_closeout.md","current_source":"artifacts/stop_gate/report_v137_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":134,"delta_ms":0,"notes":"v137 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V46-B Procedural Depth Fidelity lane: one repo-owned adeu_benchmarking package only, five released procedural-depth contracts over the released V46-A benchmark substrate, one tiny deterministic hierarchical_3x3 reference chain, trace-qualified gold/run evidence refs, frozen boolean component fidelities for plan spine active-step compilation and reintegration, explicit clean_success horizontal_plan_spine vertical_active_step_compilation reintegration and mixed outcomes, deterministic schema mirrors and v46b fixtures, canonicalized procedural-depth id helpers, and no perturbation non-regression cross-subject or downstream consumer widening."}
```

## V46B Procedural-Depth Projection Evidence

```json
{"schema":"v46b_procedural_depth_projection_evidence@1","evidence_input_path":"artifacts/agent_harness/v137/evidence_inputs/v46b_procedural_depth_projection_evidence_v137.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS137.md#v137-continuation-contract-machine-checkable","merged_pr":"#359","merge_commit":"0ac0f85297d9a73fb625b605fff7919ab1525ce4","implementation_commit":"95923f5c9845ef4088bc4375eec02eb79dc76716","review_hardening_commit":"f826779966063822bf53f84d4d52c16b5da5ddb6","implementation_packages":["adeu_benchmarking"],"benchmarking_package_root":"packages/adeu_benchmarking","benchmarking_pyproject_path":"packages/adeu_benchmarking/pyproject.toml","benchmarking_models_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/models.py","benchmarking_procedural_depth_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/procedural_depth.py","benchmarking_export_schema_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py","benchmarking_package_init_source_path":"packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py","procedural_depth_instance_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_procedural_depth_instance.v1.json","procedural_depth_gold_trace_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_procedural_depth_gold_trace.v1.json","procedural_depth_run_trace_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_procedural_depth_run_trace.v1.json","procedural_depth_metrics_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_procedural_depth_metrics.v1.json","procedural_depth_diagnostic_report_authoritative_schema_path":"packages/adeu_benchmarking/schema/adeu_procedural_depth_diagnostic_report.v1.json","procedural_depth_instance_mirror_schema_path":"spec/adeu_procedural_depth_instance.schema.json","procedural_depth_gold_trace_mirror_schema_path":"spec/adeu_procedural_depth_gold_trace.schema.json","procedural_depth_run_trace_mirror_schema_path":"spec/adeu_procedural_depth_run_trace.schema.json","procedural_depth_metrics_mirror_schema_path":"spec/adeu_procedural_depth_metrics.schema.json","procedural_depth_diagnostic_report_mirror_schema_path":"spec/adeu_procedural_depth_diagnostic_report.schema.json","released_projection_spec_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_benchmark_projection_spec.json","released_execution_context_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46a/reference_benchmark_execution_context.json","reference_instance_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_instance.json","reference_gold_trace_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_gold_trace.json","reference_clean_run_trace_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_run_trace_clean_success.json","reference_clean_metrics_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_metrics_clean_success.json","reference_clean_diagnostic_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_diagnostic_report_clean_success.json","reference_horizontal_run_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_run_trace_horizontal_plan_spine.json","reference_vertical_run_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_run_trace_vertical_active_step_compilation.json","reference_reintegration_run_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_run_trace_reintegration.json","reference_mixed_run_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_procedural_depth_run_trace_mixed.json","reference_scoring_matrix_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reference_v46b_scoring_matrix.json","reject_invalid_terminal_status_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reject_procedural_depth_run_trace_invalid_terminal_status.json","reject_mismatched_instance_ref_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reject_procedural_depth_run_trace_mismatched_instance_ref.json","reject_unsupported_event_vocabulary_fixture_path":"packages/adeu_benchmarking/tests/fixtures/v46b/reject_procedural_depth_run_trace_unsupported_event_vocabulary.json","test_reference_path":"packages/adeu_benchmarking/tests/test_benchmarking_procedural_depth.py","starter_schema_ids":["adeu_procedural_depth_instance@1","adeu_procedural_depth_gold_trace@1","adeu_procedural_depth_run_trace@1","adeu_procedural_depth_metrics@1","adeu_procedural_depth_diagnostic_report@1"],"reference_chain_key_vocabulary":["hierarchical_3x3"],"event_kind_vocabulary":["activate","complete","return"],"step_role_vocabulary":["top_level","active_parent","child"],"terminal_trace_status_vocabulary":["completed_clean","completed_with_structural_break"],"dominant_failure_family_vocabulary":["clean_success","horizontal_plan_spine","vertical_active_step_compilation","reintegration","mixed"],"component_fidelity_value_domain":[true,false],"trace_qualified_supporting_event_refs_required":true,"gold_trace_deterministically_derived_from_instance":true,"clean_success_non_failure_sentinel_frozen":true,"canonical_compute_helpers_match_materializers":true,"imported_materialization_bug_fixed":true,"targeted_local_checks":["PYTHONPATH=packages/adeu_benchmarking/src:packages/adeu_ir/src .venv/bin/python -m ruff check packages/adeu_benchmarking","PYTHONPATH=packages/adeu_benchmarking/src:packages/adeu_ir/src .venv/bin/python -m pytest packages/adeu_benchmarking/tests"],"metric_key_continuity_assertion_path":"artifacts/agent_harness/v137/evidence_inputs/metric_key_continuity_assertion_v137.json","runtime_observability_comparison_path":"artifacts/agent_harness/v137/evidence_inputs/runtime_observability_comparison_v137.json","runtime_event_stream_path":"artifacts/agent_harness/v137/runtime/evidence/local/urm_events.ndjson","notes":"v137 evidence pins the released V46-B concrete Procedural Depth Fidelity seam on main: one repo-owned adeu_benchmarking package only, five released procedural-depth contracts over the released V46-A family spec projection spec and execution context substrate, one tiny deterministic hierarchical_3x3 reference chain, deterministic gold-trace derivation from the released instance, deterministic run scoring with frozen boolean component fidelities and trace-qualified supporting refs, positive clean_success horizontal_plan_spine vertical_active_step_compilation reintegration and mixed fixtures, authoritative and mirrored schema export, canonical compute/materialize parity after review hardening, and no perturbation non-regression cross-subject or downstream consumer widening."}
```

## Recommendation (Post v137)

- gate decision:
  - `V46B_PROCEDURAL_DEPTH_PROJECTION_COMPLETE_ON_MAIN`
- rationale:
  - `v137` closes the first concrete Procedural Depth Fidelity projection seam on
    `main` after the benchmark substrate was already released in `V46-A`.
  - the shipped slice stayed narrow and projection-first:
    - one repo-owned package
    - five released procedural-depth contracts only
    - one tiny deterministic hierarchical `3x3` reference chain only
    - deterministic gold-trace derivation and deterministic run scoring only
    - explicit trace-qualified supporting evidence only
    - frozen boolean component fidelities plus bounded dominant-family diagnosis only
    - no perturbation or non-regression widening
    - no cross-subject comparison or downstream consumer seam
  - review hardening stayed bounded and materially improved repo alignment:
    `f826779966063822bf53f84d4d52c16b5da5ddb6` canonicalized the exported
    procedural-depth `compute_*_id` helpers so semantically equivalent payloads now
    hash the same way materialization and validation do.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat at `0 ms` delta versus the `v136` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v29.md` should now be read with `V46-B` closed on
    `main` and `V46-C` selected as the next branch-local default path.
