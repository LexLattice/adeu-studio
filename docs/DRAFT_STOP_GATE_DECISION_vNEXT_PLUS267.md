# Draft Stop-Gate Decision vNext+267

Status: post-closeout decision for `PB-MATRIX-INCLUSION-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS267.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+267` /
  `PB-MATRIX-INCLUSION-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS267.md`.
- It does not authorize matrix revision registration, revision readiness
  summaries, post-inclusion handoffs, family closeout, result projection,
  matrix summary, local case execution, probe execution, batch command
  execution, candidate materialization, official ProgramBench participation,
  official runner/evaluator integration, hidden-test handling, hidden-test
  inference, hidden-test equivalence, benchmark scoring, benchmark truth,
  baseline comparison, pass rate, solve rate, success rate, model ranking,
  leaderboard standing, official submission authority, second retry
  authority, retry-chain authority, future-family selection, product
  authorization, graph-memory authority, release authority, or recursive
  policy amendment.

## Evidence Source

- merged implementation PR:
  - `#495` (`Implement PB-MATRIX-INCLUSION-0-B`)
- merge commit:
  - `ff5f181f07311c5174095ff87ade97a84566a3da`
- merged-at timestamp:
  - `2026-05-09T18:07:41Z`
- implementation commit integrated by the merge:
  - `68714007bd48e05b48d57f700631bf0ec80d9b51`
    (`Implement PB-MATRIX-INCLUSION-0-B`)
- implementation verification recorded before merge:
  - focused `PB-MATRIX-INCLUSION-0-B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=267`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v267_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v267_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v267_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v267/evidence_inputs/metric_key_continuity_assertion_v267.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v267/evidence_inputs/runtime_observability_comparison_v267.json`
  - `PB-MATRIX-INCLUSION-0-B` closeout evidence input:
    `artifacts/agent_harness/v267/evidence_inputs/pb_matrix_inclusion_0b_closeout_evidence_v267.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v267/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS267_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-MATRIX-INCLUSION-0-B` merged on `main` | required | `pass` | PR `#495`, merge commit `ff5f181f07311c5174095ff87ade97a84566a3da` |
| Implementation stayed in the matrix-inclusion lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected B surfaces shipped | required | `pass` | amendment plan, case delta manifest, comparability delta review, contamination delta review, and inclusion decision record shapes shipped |
| Released A rows are required | required | `pass` | B bundle validator requires the released A request, candidate intake, eligibility, control, and guardrail rows |
| A-eligible candidates are accounted exactly once | required | `pass` | amendment plan and delta manifest must match the A eligible lineage set |
| Delta rows bind to A candidate lineage identity | required | `pass` | delta lineage hashes, prior membership status, and dedupe status must match A candidate rows |
| Comparability hash pairs are force-bearing | required | `pass` | unchanged posture requires equal base/candidate hashes; changed posture requires hash delta |
| Inclusion decisions remain governance/accounting decisions | required | `pass` | decision basis rows reject performance language and must match included/deferred/rejected outcome buckets |
| Decision basis matches delta reason | required | `pass` | B bundle rejects mismatch between decision basis kind and case delta reason |
| Contamination transfer by summary is rejected | required | `pass` | hidden, forbidden, source-derived, evaluator-derived, and similar content markers are rejected in B notes |
| Clean contamination is required before inclusion | required | `pass` | B bundle rejects included cases when contamination transfer is blocked |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no matrix revision registration, execution, projection, scoring, baseline comparison, model ranking, official authority, or future-family selection shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v267_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v267/evidence_inputs/metric_key_continuity_assertion_v267.json` records exact keyset equality versus `v266` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v267/evidence_inputs/runtime_observability_comparison_v267.json` records `63 ms` baseline, `101 ms` current, `38 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v267_closeout_stop_gate_summary@1",
  "arc": "vNext+267",
  "target_path": "PB-MATRIX-INCLUSION-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v266": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 101,
  "runtime_observability_delta_ms": 38
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v266_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v267_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+266","baseline_elapsed_ms":63,"baseline_source":"artifacts/stop_gate/report_v266_closeout.md","current_arc":"vNext+267","current_elapsed_ms":101,"current_source":"artifacts/stop_gate/report_v267_closeout.md","delta_ms":38,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+267","amendment_plan_requires_released_a_refs":true,"baseline_comparison_authority_granted":false,"benchmark_truth_authority_granted":false,"case_delta_manifest_accounts_all_a_eligible_candidates":true,"changed_comparability_requires_hash_delta":true,"clean_contamination_required_for_inclusion":true,"closed_slice":"PB-MATRIX-INCLUSION-0-B","comparability_hash_pairs_bound":true,"contamination_summary_laundering_rejected":true,"decision_basis_matches_case_delta_reason":true,"decision_basis_matches_recorded_outcome":true,"execution_authority_granted":false,"family":"PB-MATRIX-INCLUSION-0","future_family_selection_granted":false,"implementation_commits":["68714007bd48e05b48d57f700631bf0ec80d9b51"],"implementation_package":"packages/adeu_benchmarking","inclusion_decisions_are_local_accounting_only":true,"matrix_revision_registration_granted":false,"merge_commit":"ff5f181f07311c5174095ff87ade97a84566a3da","merged_at":"2026-05-09T18:07:41Z","merged_pr":"#495","metric_key_continuity_assertion_path":"artifacts/agent_harness/v267/evidence_inputs/metric_key_continuity_assertion_v267.json","model_ranking_authority_granted":false,"official_programbench_authority_granted":false,"reference_fixture_root":"apps/api/fixtures/benchmarking/vnext_plus267","result_projection_authority_granted":false,"runtime_event_stream_path":"artifacts/agent_harness/v267/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v267/evidence_inputs/runtime_observability_comparison_v267.json","schema":"pb_matrix_inclusion_0b_closeout_evidence@1","selected_record_shapes":["programbench_local_matrix_amendment_plan@1","programbench_local_matrix_case_delta_manifest@1","programbench_local_matrix_comparability_delta_review@1","programbench_local_matrix_contamination_delta_review@1","programbench_local_matrix_inclusion_decision_record@1"],"soft_performance_decision_basis_rejected":true,"test_reference_path":"packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0b.py","unchanged_comparability_requires_equal_hashes":true,"verification_commands":[".venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0b.py -q","make check","make arc-closeout-check ARC=267"]}
```

## Recommendation

- gate decision:
  - `PB_MATRIX_INCLUSION_0B_AMENDMENT_AND_DECISION_COMPLETE_ON_MAIN`
- rationale:
  - `v267` closes the bounded `PB-MATRIX-INCLUSION-0-B` amendment plan,
    case delta, comparability delta, contamination delta, and inclusion
    decision seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - five local cleanroom matrix-inclusion B record surfaces
    - released A rows are required before B validates
    - A-eligible candidates are accounted exactly once
    - delta rows bind to A candidate hashes and membership/dedupe posture
    - comparability posture is checked against base/candidate hash equality
    - contamination transfer remains fail-closed and content-redacted
    - decision basis rows remain governance/accounting only and match both
      their outcome buckets and delta reasons
    - no matrix revision registration, execution, result projection,
      benchmark scoring, baseline comparison, model ranking, official
      ProgramBench authority, or future-family selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- family status:
  - `PB-MATRIX-INCLUSION-0` remains open; proceed to `PB-MATRIX-INCLUSION-0-C`.
