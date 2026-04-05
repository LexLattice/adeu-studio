# Draft Stop-Gate Decision (Post vNext+132)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS132.md`

Status: draft decision note (post-hoc closeout capture, April 5, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS132.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v132_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+132` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS132.md`.
- This note captures bounded `V44-B` structural-failure taxonomy evidence only; it
  does not authorize paired-condition differential diagnosis, model-profile
  aggregation, benchmark scoring, or benchmark-family projection by itself.
- Canonical `V44-B` release in `v132` is carried by the shipped
  `packages/adeu_reasoning_assessment` package additions, authoritative and mirrored
  `adeu_structural_failure_taxonomy@1` schema export, deterministic `v44b`
  fixtures/tests, and the canonical
  `v44b_structural_failure_taxonomy_evidence@1` evidence input under
  `artifacts/agent_harness/v132/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` now marks `V44-B`
  closed on `main` and advances the branch-local default next path to `V44-C`; it
  does not complete the whole `V44` family by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#354` (`feat(v132): add structural failure taxonomy`)
- arc-completion merge commit: `8e24715ffeb5740fe95bd38f71dc418578097b52`
- merged-at timestamp: `2026-04-05T11:52:27Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v132_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v132_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v132_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v132/evidence_inputs/metric_key_continuity_assertion_v132.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v132/evidence_inputs/runtime_observability_comparison_v132.json`
  - `V44-B` release evidence input:
    `artifacts/agent_harness/v132/evidence_inputs/v44b_structural_failure_taxonomy_evidence_v132.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS132_EDGES.md`

## Exit-Criteria Check (vNext+132)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V44-B` merged with green CI | required | `pass` | PR `#354`, merge commit `8e24715ffeb5740fe95bd38f71dc418578097b52`, checks `python/web/lean-formal = pass` |
| `packages/adeu_reasoning_assessment` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_reasoning_assessment` only |
| Authoritative and mirror taxonomy schemas ship deterministically | required | `pass` | `packages/adeu_reasoning_assessment/schema/adeu_structural_failure_taxonomy.v1.json`, `spec/adeu_structural_failure_taxonomy.schema.json`, and schema export replay coverage |
| Clean and lawful-blocked taxonomy references validate cleanly | required | `pass` | `reference_structural_failure_taxonomy_clean.json`, `reference_structural_failure_taxonomy_blocked.json`, and taxonomy model/helper coverage |
| Positive hierarchy-aware taxonomy references validate for the three starter families | required | `pass` | `reference_structural_failure_taxonomy_plan_spine_drift.json`, `reference_structural_failure_taxonomy_active_step_decomposition_failure.json`, `reference_structural_failure_taxonomy_reintegration_failure.json`, and targeted taxonomy tests |
| Invalid early closure normalization remains explicit and bounded | required | `pass` | `reference_structural_failure_taxonomy_invalid_early_closure.json` and mapping-law coverage |
| Reject fixtures fail closed for unsupported break-tag mapping and blocked trace coerced into failure-family output | required | `pass` | committed reject fixtures plus `test_reasoning_assessment_taxonomy.py` coverage |
| Blocked posture remains distinct from normalized failure output | required | `pass` | released `taxonomy_status` vocabulary plus blocked fixture and reject fixture coverage |
| Event-order-first failure-family ordering is deterministic | required | `pass` | released ordering law in `taxonomy.py`, mapping-matrix replay, and reference taxonomy fixture ordering |
| No profile, differential, benchmark, or one-number structural-fidelity fields ship in `V44-B` | required | `pass` | released schema/package exports contain taxonomy surfaces only |
| Root `spec/` mirrors are claimed in docs and actually shipped | required | `pass` | merged `spec/adeu_structural_failure_taxonomy.schema.json` |
| Local targeted validation passed for the touched package lane | required | `pass` | PR lane ran `ruff` plus `pytest packages/adeu_reasoning_assessment/tests` (`17 passed`) |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v132_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v132/evidence_inputs/metric_key_continuity_assertion_v132.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v132/evidence_inputs/runtime_observability_comparison_v132.json` |

## Stop-Gate Summary

```json
{
  "schema": "v132_closeout_stop_gate_summary@1",
  "arc": "vNext+132",
  "target_path": "V44-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v131": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 126,
  "runtime_observability_delta_ms": 40
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v131_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v132_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+131","current_arc":"vNext+132","baseline_source":"artifacts/stop_gate/report_v131_closeout.md","current_source":"artifacts/stop_gate/report_v132_closeout.md","baseline_elapsed_ms":86,"current_elapsed_ms":126,"delta_ms":40,"notes":"v132 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V44-B structural failure taxonomy lane: one repo-owned adeu_reasoning_assessment package only, one released adeu_structural_failure_taxonomy@1 contract, deterministic taxonomy normalization over released V44-A probe/trace contracts only, blocked preserved as non-failure, event-order-first failure-family ordering, explicit hierarchy-aware positive fixtures for plan_spine_drift active_step_decomposition_failure and reintegration_failure, explicit invalid_early_closure normalization, authoritative and mirrored taxonomy schema export, and no profile or benchmark scoring surfaces."}
```

## V44B Structural Failure Taxonomy Evidence

```json
{"schema":"v44b_structural_failure_taxonomy_evidence@1","evidence_input_path":"artifacts/agent_harness/v132/evidence_inputs/v44b_structural_failure_taxonomy_evidence_v132.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS132.md#v132-continuation-contract-machine-checkable","merged_pr":"#354","merge_commit":"8e24715ffeb5740fe95bd38f71dc418578097b52","implementation_packages":["adeu_reasoning_assessment"],"reasoning_assessment_package_root":"packages/adeu_reasoning_assessment","reasoning_assessment_pyproject_path":"packages/adeu_reasoning_assessment/pyproject.toml","reasoning_assessment_models_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py","reasoning_assessment_taxonomy_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/taxonomy.py","reasoning_assessment_export_schema_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py","reasoning_assessment_package_init_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py","structural_failure_taxonomy_authoritative_schema_path":"packages/adeu_reasoning_assessment/schema/adeu_structural_failure_taxonomy.v1.json","structural_failure_taxonomy_mirror_schema_path":"spec/adeu_structural_failure_taxonomy.schema.json","accepted_clean_taxonomy_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_failure_taxonomy_clean.json","accepted_blocked_taxonomy_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_failure_taxonomy_blocked.json","accepted_plan_spine_drift_taxonomy_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_failure_taxonomy_plan_spine_drift.json","accepted_active_step_decomposition_failure_taxonomy_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_failure_taxonomy_active_step_decomposition_failure.json","accepted_reintegration_failure_taxonomy_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_failure_taxonomy_reintegration_failure.json","accepted_invalid_early_closure_taxonomy_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_failure_taxonomy_invalid_early_closure.json","mapping_matrix_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_v44b_taxonomy_mapping_matrix.json","reject_unsupported_break_tag_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reject_structural_reasoning_trace_unsupported_break_tag.json","reject_blocked_with_failure_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reject_structural_failure_taxonomy_blocked_with_failure_family.json","supporting_trace_plan_spine_drift_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_reasoning_trace_plan_spine_drift.json","supporting_trace_active_step_decomposition_failure_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_reasoning_trace_active_step_decomposition_failure.json","supporting_trace_reintegration_failure_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_reasoning_trace_reintegration_failure.json","supporting_trace_invalid_early_closure_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44b/reference_structural_reasoning_trace_invalid_early_closure.json","test_reference_path":"packages/adeu_reasoning_assessment/tests/test_reasoning_assessment_taxonomy.py","taxonomy_status_vocabulary":["completed_clean_no_failure","blocked_lawful_insufficiency","normalized_structural_failure"],"failure_family_vocabulary":["lane_collapse","branch_collapse","plan_spine_drift","active_step_decomposition_failure","reintegration_failure","invalid_early_closure","non_local_repair_drift"],"blocked_posture_preserved":true,"event_order_first_occurrence_ordering":true,"profile_fields_forbidden":true,"benchmark_projection_forbidden":true,"review_cleanup_commit":"dd5cd22","metric_key_continuity_assertion_path":"artifacts/agent_harness/v132/evidence_inputs/metric_key_continuity_assertion_v132.json","runtime_observability_comparison_path":"artifacts/agent_harness/v132/evidence_inputs/runtime_observability_comparison_v132.json","runtime_event_stream_path":"artifacts/agent_harness/v132/runtime/evidence/local/urm_events.ndjson","notes":"v132 evidence pins the released V44-B taxonomy-first seam on main: one repo-owned adeu_reasoning_assessment package only, one released adeu_structural_failure_taxonomy@1 contract, deterministic normalization over released V44-A probes and traces only, blocked preserved as non-failure, explicit hierarchy-aware positive fixtures for plan_spine_drift active_step_decomposition_failure and reintegration_failure, explicit invalid_early_closure normalization, explicit fail-closed behavior for unsupported break-tag mappings and blocked/failure posture collisions, no paired-condition differential, no profile aggregation, and no benchmark scoring projection."}
```

## Recommendation (Post v132)

- gate decision:
  - `V44B_STRUCTURAL_FAILURE_TAXONOMY_COMPLETE_ON_MAIN`
  - `V44_REASONING_ASSESSMENT_FAMILY_CONTINUES_WITH_V44C_NEXT`
- rationale:
  - `v132` closes the bounded taxonomy-first seam on `main` only after the
    contract-first `V44-A` probe/trace substrate was already released.
  - the released slice stays narrow and evidentiary: one package, one taxonomy
    contract, deterministic mapping law over released `V44-A` structure only, and no
    profile, differential, or benchmark surfaces.
  - blocked remains a real non-failure outcome, not a taxonomy bucket, and invalid
    early closure remains a separate normalized structural failure family.
  - the starter hierarchy-aware contribution is real law rather than vocabulary only:
    direct positive fixtures now exercise `plan_spine_drift`,
    `active_step_decomposition_failure`, and `reintegration_failure`.
  - review follow-up stayed non-semantic: `dd5cd22` sorted the package export surface
    only.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability regressed informationally by `+40 ms` versus the `v131`
    baseline, but the stop-gate remained fully passing and stable.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` should now be read with `V44-B` closed on
    `main` and `V44-C` as the branch-local default next path.
