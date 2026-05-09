# Draft Stop-Gate Decision vNext+261

Status: post-closeout decision for `PB-MATRIX-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS261.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+261` / `PB-MATRIX-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS261.md`.
- It does not authorize matrix summary, post-matrix handoff, family closeout,
  local case execution, batch command execution, candidate materialization,
  official ProgramBench participation, official runner/evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  benchmark scoring, benchmark truth, pass rate, solve rate, success rate,
  model ranking, leaderboard standing, official submission authority, second
  retry authority, retry-chain authority, future-family selection, product
  authorization, graph-memory authority, release authority, or recursive
  policy amendment.

## Evidence Source

- merged implementation PR:
  - `#489` (`Implement PB-MATRIX-0-B result projection`)
- arc-completion merge commit:
  - `cb6b6f51fceba3f57bba3aea2db973b8f2ad33a8`
- merged-at timestamp:
  - `2026-05-09T02:21:12Z`
- implementation commits integrated by the merge:
  - `d118589d7cda5c818e60d3bb26d48880bf2a5648`
    (`Implement PB-MATRIX-0-B result projection`)
  - `bf4da0ef38b603b9f885f4713dc608a6d28ef6cf`
    (`Harden PB-MATRIX-0-B projection validation`)
- implementation verification recorded before merge:
  - focused `PB-MATRIX-0-B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=261`
  - `make arc-start-check ARC=262`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v261_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v261_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v261_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v261/evidence_inputs/metric_key_continuity_assertion_v261.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v261/evidence_inputs/runtime_observability_comparison_v261.json`
  - `PB-MATRIX-0-B` projection closeout evidence input:
    `artifacts/agent_harness/v261/evidence_inputs/pb_matrix_0b_projection_closeout_evidence_v261.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v261/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS261_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-MATRIX-0-B` merged on `main` | required | `pass` | PR `#489`, merge commit `cb6b6f51fceba3f57bba3aea2db973b8f2ad33a8` |
| Implementation stayed in the local cleanroom case-matrix lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-MATRIX-0-B` surfaces shipped | required | `pass` | result projection, observation ledger, coverage register, and contamination register shapes shipped |
| B consumes released `PB-MATRIX-0-A` basis | required | `pass` | bundle validation requires A request, inclusion manifest, eligibility review, control contract, and guardrail refs |
| Projection rows cover only A-included cases | required | `pass` | validators require projected cases to match A included and eligible case refs |
| Retry-settlement projections bind to A-admitted settlements | required | `pass` | review hardening rejects retry projections whose source result differs from the A manifest settlement ref |
| Projection remains derived local posture, not new outcome truth | required | `pass` | projection authority posture and reject fixtures block new outcome truth |
| Projection gaps remain explicit and ordered | required | `pass` | validators require gap refs to match row order without runtime sorting normalization |
| Observation ledger remains local and non-ranking | required | `pass` | observation row/ledger validators reject ranking/scoring language and partition blocked/unblocked rows |
| Coverage register stays local-only | required | `pass` | coverage denominator is declared local matrix cases only and hidden-test coverage is rejected |
| Contamination register redacts forbidden detail | required | `pass` | contamination detail posture rejects hidden/forbidden names, paths, excerpts, summaries, and source clues |
| B does not emit C artifacts | required | `pass` | no matrix summary, handoff, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, batch execution, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v261_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v261/evidence_inputs/metric_key_continuity_assertion_v261.json` records exact keyset equality versus `v260` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v261/evidence_inputs/runtime_observability_comparison_v261.json` records `108 ms` baseline, `98 ms` current, `-10 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v261_closeout_stop_gate_summary@1",
  "arc": "vNext+261",
  "target_path": "PB-MATRIX-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v260": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 98,
  "runtime_observability_delta_ms": -10
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v260_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v261_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+260","baseline_elapsed_ms":108,"baseline_source":"artifacts/stop_gate/report_v260_closeout.md","current_arc":"vNext+261","current_elapsed_ms":98,"current_source":"artifacts/stop_gate/report_v261_closeout.md","delta_ms":-10,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+261","benchmark_truth_authority_granted":false,"closed_slice":"PB-MATRIX-0-B","coverage_hidden_test_claim_rejected":true,"family":"PB-MATRIX-0","focused_test":"packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0b.py","future_family_selection_granted":false,"implementation_package":"packages/adeu_benchmarking","matrix_scoring_authority_granted":false,"merged_at":"2026-05-09T02:21:12Z","merged_pr":"#489","model_ranking_authority_granted":false,"official_programbench_authority_granted":false,"projection_rows_bound_to_a_included_cases":true,"projection_rows_bound_to_a_retry_settlement":true,"projection_rows_derived_not_new_truth":true,"reference_fixture_root":"apps/api/fixtures/benchmarking/vnext_plus261","schema":"pb_matrix_0b_projection_closeout_evidence@1","selected_record_shapes":["programbench_local_case_matrix_result_projection@1","programbench_local_case_matrix_observation_ledger@1","programbench_local_case_matrix_coverage_register@1","programbench_local_case_matrix_contamination_register@1"],"soft_scoring_language_rejected":true,"verification_commands":[".venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0b.py -q","make check","make arc-closeout-check ARC=261"]}
```

## Recommendation

- gate decision:
  - `PB_MATRIX_0B_PROJECTION_COMPLETE_ON_MAIN`
- rationale:
  - `v261` closes the bounded `PB-MATRIX-0-B` projection and observation seam
    on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four local cleanroom case-matrix projection/observation record surfaces
    - released `PB-MATRIX-0-A` rows required before B bundle validation
    - projection rows must match A-included cases
    - retry-settlement projections must match the A-admitted settlement ref
    - projection remains derived local posture, not new outcome truth
    - coverage denominator remains local matrix cases only
    - hidden-test coverage, benchmark score, model ranking, soft scoring
      language, and contamination detail leaks are rejected
    - no matrix summary, post-matrix handoff, family closeout, batch
      execution, official ProgramBench participation, hidden-test handling,
      second retry authority, or future-family selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- next bounded slice:
  - `PB-MATRIX-0-C`
