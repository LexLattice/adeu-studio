# Draft Stop-Gate Decision (Post vNext+207)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS207.md`

Status: draft decision note (post-closeout capture, April 29, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS207.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v207_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+207` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS207.md`.
- This note captures bounded `V74-B` closeout evidence only on `main`; it does
  not authorize `V74-C` decision visibility contracts, ratification-review
  workbench projection, post-projection handoff, `V75` dispatch, live UI,
  product authorization, runtime permission, release authority, external
  contest participation, ratification, adoption, exception resolution, global
  model ranking, model selection, benchmark truth, or recursive self-approval.
- Canonical `V74-B` shipment in `v207` is carried by bounded
  `adeu_repo_description` typed adjudication case-view, model-output comparison
  projection, and projection exception visibility register models, validators,
  schema exports, deterministic `vnext_plus207` reference and reject fixtures,
  and canonical `v74b_operator_projection_evidence@1` evidence input under
  `artifacts/agent_harness/v207/evidence_inputs/`.

## Evidence Source

- merged implementation PR:
  - `#435` (`[codex] Implement V74-B operator projection surfaces`)
- arc-completion merge commit:
  - `445eac2982ebb8a3f97b386419a3c066d9c06b08`
- merged-at timestamp:
  - `2026-04-29T19:31:13Z`
- implementation commits integrated by the merge:
  - `b0f9037753b09300dd6ad4a02e55a40e8dadd523`
    (`Implement V74-B operator projection surfaces`)
  - `8cebfb9748d1876c061672b649bfa8cba88c185f`
    (`Harden V74-B projection note validation`)
- implementation verification recorded before PR / update:
  - focused pytest
  - V74-B plus export-schema pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=207`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v207_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v207_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v207_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v207/evidence_inputs/metric_key_continuity_assertion_v207.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v207/evidence_inputs/runtime_observability_comparison_v207.json`
  - `V74-B` operator projection evidence input:
    `artifacts/agent_harness/v207/evidence_inputs/v74b_operator_projection_evidence_v207.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v207/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS207_EDGES.md`

## Exit-Criteria Check (vNext+207)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V74-B` merged on `main` | required | `pass` | PR `#435`, merge commit `445eac2982ebb8a3f97b386419a3c066d9c06b08` |
| Implementation stayed in the repo-description lane | required | `pass` | merged implementation package is `adeu_repo_description` |
| Selected typed-case, model-comparison, and exception-visibility surfaces shipped | required | `pass` | `repo_typed_adjudication_case_view@1`, `repo_model_output_comparison_projection@1`, and `repo_projection_exception_visibility_register@1` |
| Released `V74-A` case-view / source-index / guardrail substrate is consumed | required | `pass` | V74-B rows reference released `vnext_plus206` fixture material |
| Conceptual-diff support remains lineage, not released schema | required | `pass` | conceptual-diff support-as-released-schema reject fixture passed |
| Model-output comparison stays fixed-substrate, non-benchmark, and non-selection | required | `pass` | prompt/source/provenance/axis/global-ranking reject fixtures passed |
| Comparison axes are structured and source-bound | required | `pass` | missing source evidence and missing bounded guardrail reject fixtures passed |
| Exception rows remain visible and unresolved by `V74-B` | required | `pass` | exception omission and exception resolution reject fixtures passed |
| Product-pressure typed cases stay non-authorizing | required | `pass` | product-authorization reject fixture passed |
| Typed cases cannot mint new ratification or outcome verdicts | required | `pass` | typed-case new-ratification reject fixture passed |
| Comparison projection cannot authorize implementation, release, product, runtime, dispatch, or external contest participation | required | `pass` | comparison-dispatch reject fixture passed |
| `V74-C`, `V75`, live UI, product authorization, release, runtime, and dispatch remain deferred | required | `pass` | closeout evidence records all deferred selections as false |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v207_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v207/evidence_inputs/metric_key_continuity_assertion_v207.json` records exact keyset equality versus `v206` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v207/evidence_inputs/runtime_observability_comparison_v207.json` records `107 ms` baseline, `87 ms` current, `-20 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v207_closeout_stop_gate_summary@1",
  "arc": "vNext+207",
  "target_path": "V74-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v206": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 87,
  "runtime_observability_delta_ms": -20
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v206_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v207_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+206","baseline_elapsed_ms":107,"baseline_source":"artifacts/stop_gate/report_v206_closeout.md","current_arc":"vNext+207","current_elapsed_ms":87,"current_source":"artifacts/stop_gate/report_v207_closeout.md","delta_ms":-20,"notes":"v207 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while closing the bounded V74-B operator projection slice on main: repo-owned adeu_repo_description package only, three repo_* V74-B surfaces, source-bound consumption of released V74-A case-view/source-index/guardrail substrate, conceptual-diff support kept as lineage rather than released schema, model-output comparison kept fixed-substrate/non-benchmark/non-selection, exception rows kept visible and unresolved, and no V74-C visibility contract, review workbench, post-projection handoff, live UI, product authorization, ratification, release, runtime permission, dispatch, external contest participation, global model ranking, or recursive self-approval.","schema":"runtime_observability_comparison@1"}
```

## V74B Operator Projection Evidence

```json
{"comparison_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_model_output_comparison_projection.v1.json","comparison_authorizes_dispatch_rejected":true,"comparison_axis_requires_bounded_guardrail":true,"comparison_axis_requires_source_evidence":true,"comparison_mirror_schema_path":"spec/repo_model_output_comparison_projection.schema.json","comparison_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus207/repo_model_output_comparison_projection_v207_reference.json","comparison_requires_model_output_provenance_rows":true,"comparison_requires_prompt_source_refs":true,"conceptual_diff_support_as_released_schema_rejected":true,"consumed_record_shapes":["repo_operator_projection_case_view@1","repo_operator_projection_source_index@1","repo_operator_projection_non_authority_guardrail@1"],"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS207.md#machine-checkable-contract","evidence_input_path":"artifacts/agent_harness/v207/evidence_inputs/v74b_operator_projection_evidence_v207.json","exception_omission_rejected":true,"exception_register_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_projection_exception_visibility_register.v1.json","exception_register_mirror_schema_path":"spec/repo_projection_exception_visibility_register.schema.json","exception_register_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus207/repo_projection_exception_visibility_register_v207_reference.json","exception_resolution_rejected":true,"implementation_commits":["b0f9037753b09300dd6ad4a02e55a40e8dadd523","8cebfb9748d1876c061672b649bfa8cba88c185f"],"implementation_packages":["adeu_repo_description"],"implementation_source_path":"packages/adeu_repo_description/src/adeu_repo_description/operator_projection.py","local_full_python_gate":"make check","merge_commit":"445eac2982ebb8a3f97b386419a3c066d9c06b08","merged_at":"2026-04-29T19:31:13Z","merged_pr":"#435","metric_key_continuity_assertion_path":"artifacts/agent_harness/v207/evidence_inputs/metric_key_continuity_assertion_v207.json","model_output_global_ranking_rejected":true,"notes":"v207 evidence pins the bounded V74-B closeout seam on main: typed adjudication case views, model-output comparison projections, and exception visibility registers consume released V74-A projection substrate; conceptual-diff support remains lineage only; comparison axes are structured and non-benchmark; model-output provenance is fixed to prompt/model/output/run context; exceptions remain visible and unresolved; and V74-C/V75/product/release/runtime/dispatch authorities remain deferred.","package_export_surface_path":"packages/adeu_repo_description/src/adeu_repo_description/__init__.py","product_authorization_rejected":true,"reject_fixture_dir":"apps/api/fixtures/repo_description/vnext_plus207","runtime_event_stream_path":"artifacts/agent_harness/v207/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v207/evidence_inputs/runtime_observability_comparison_v207.json","schema":"v74b_operator_projection_evidence@1","schema_export_source_path":"packages/adeu_repo_description/src/adeu_repo_description/export_schema.py","selected_decision_visibility_contract_for_v74b":false,"selected_external_contest_participation_for_v74b":false,"selected_family_closeout_alignment_for_v74b":false,"selected_live_ui_or_operator_command_surface_for_v74b":false,"selected_post_projection_handoff_for_v74b":false,"selected_product_authorization_for_v74b":false,"selected_ratification_review_workbench_for_v74b":false,"selected_record_shapes":["repo_typed_adjudication_case_view@1","repo_model_output_comparison_projection@1","repo_projection_exception_visibility_register@1"],"selected_release_authority_for_v74b":false,"selected_runtime_permission_or_dispatch_for_v74b":false,"test_reference_path":"packages/adeu_repo_description/tests/test_operator_projection_v74b.py","typed_case_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_typed_adjudication_case_view.v1.json","typed_case_mirror_schema_path":"spec/repo_typed_adjudication_case_view.schema.json","typed_case_new_ratification_rejected":true,"typed_case_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus207/repo_typed_adjudication_case_view_v207_reference.json"}
```

## Recommendation (Post v207)

- gate decision:
  - `V74B_TYPED_ADJUDICATION_MODEL_COMPARISON_EXCEPTION_VISIBILITY_COMPLETE_ON_MAIN`
- rationale:
  - `v207` closes the bounded `V74-B` operator projection slice on `main`;
  - the shipped slice stayed properly bounded:
    - same repo-owned implementation package (`adeu_repo_description`) only
    - three `repo_*` V74-B record surfaces
    - source-bound consumption of released `V74-A` projection rows
    - conceptual-diff support projected as lineage only, not released schema
    - structured comparison axes with bounded horizons and source refs
    - model-output comparison remains fixed-substrate, non-benchmark,
      non-selection, and non-global
    - exception visibility rows keep blockers visible and unresolved
    - no decision visibility contract, review workbench projection,
      post-projection handoff, live UI, product authorization, ratification,
      release, runtime permission, dispatch, external contest participation,
      benchmark truth, or recursive self-approval
  - stop-gate schema-family and metric-key continuity stayed intact.
  - runtime observability remained informational-only.
  - `V74-B` is now closed on `main`.
  - `V74` remains open for `V74-C`: decision visibility contract,
    ratification-review workbench projection, post-projection handoff, and
    family closeout alignment.
