# Draft Stop-Gate Decision vNext+260

Status: post-closeout decision for `PB-MATRIX-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS260.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+260` / `PB-MATRIX-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS260.md`.
- It does not authorize per-case result projection, observation ledger,
  coverage register, contamination register, matrix summary, handoff,
  family closeout, official ProgramBench participation, official task
  execution, official runner/evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, benchmark scoring,
  benchmark truth, pass rate, solve rate, success rate, model ranking,
  leaderboard standing, official submission authority, batch execution,
  second retry authority, retry-chain authority, future-family selection,
  product authorization, graph-memory authority, release authority, or
  recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#488` (`Implement PB-MATRIX-0-A matrix intake`)
- arc-completion merge commit:
  - `ac11778b96bcecfacd55d5516c074ef22e4dde33`
- merged-at timestamp:
  - `2026-05-09T01:38:31Z`
- implementation commits integrated by the merge:
  - `f58bbb605b32cc59cbcda4dca4a35e933c0bdcc6`
    (`Implement PB-MATRIX-0-A matrix intake`)
  - `769a195836276b4714091aa984b4de3d26dc980d`
    (`Harden PB-MATRIX-0-A review validation`)
- implementation verification recorded before merge:
  - focused `PB-MATRIX-0-A` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=260`
  - `make arc-start-check ARC=261`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v260_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v260_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v260_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v260/evidence_inputs/metric_key_continuity_assertion_v260.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v260/evidence_inputs/runtime_observability_comparison_v260.json`
  - `PB-MATRIX-0-A` matrix-intake closeout evidence input:
    `artifacts/agent_harness/v260/evidence_inputs/pb_matrix_0a_matrix_intake_closeout_evidence_v260.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v260/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-MATRIX-0-A` merged on `main` | required | `pass` | PR `#488`, merge commit `ac11778b96bcecfacd55d5516c074ef22e4dde33` |
| Implementation stayed in the local cleanroom case-matrix lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-MATRIX-0-A` surfaces shipped | required | `pass` | matrix request, inclusion manifest, lineage eligibility review, control contract, and non-authority guardrail shapes shipped |
| Prior `PB-TRIAL-0` / optional `PB-RETRY-0` lineage is required for included cases | required | `pass` | bundle validation consumes released local trial and retry closeout/lineage refs |
| Included cases are row-shaped and source-bound | required | `pass` | inclusion manifest requires explicit case candidate rows, boundary hashes, lineage refs, origin posture, and inclusion decisions |
| Eligibility rows cover every candidate case | required | `pass` | review hardening requires lineage eligibility rows for every manifest candidate, not only included cases |
| Case aggregation remains non-scoring | required | `pass` | aggregate-count posture stays inventory/accounting-only; score/pass-rate language is rejected |
| Matrix controls remain non-ranking | required | `pass` | multi-profile or multi-control matrices require comparability-accounting-only posture on both profile and matrix comparability axes |
| Matrix controls cannot grant batch execution | required | `pass` | control and guardrail validators reject command execution, batch execution, official evaluator access, hidden-test access, source lookup, and future-family authority |
| Duplicate forbidden-action and non-authority rows are rejected | required | `pass` | review hardening rejects duplicate `action_kind` and `authority_kind` rows |
| A does not emit B/C artifacts | required | `pass` | no result projection, observation ledger, coverage register, contamination register, matrix summary, handoff, or closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, batch execution, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v260_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v260/evidence_inputs/metric_key_continuity_assertion_v260.json` records exact keyset equality versus `v259` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v260/evidence_inputs/runtime_observability_comparison_v260.json` records `104 ms` baseline, `108 ms` current, `4 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v260_closeout_stop_gate_summary@1",
  "arc": "vNext+260",
  "target_path": "PB-MATRIX-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v259": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 108,
  "runtime_observability_delta_ms": 4
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v259_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v260_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+259","baseline_elapsed_ms":104,"baseline_source":"artifacts/stop_gate/report_v259_closeout.md","current_arc":"vNext+260","current_elapsed_ms":108,"current_source":"artifacts/stop_gate/report_v260_closeout.md","delta_ms":4,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+260","aggregate_count_posture_inventory_only":true,"benchmark_truth_authority_granted":false,"case_candidate_rows_required":true,"closed_slice":"PB-MATRIX-0-A","eligible_rows_cover_all_candidates":true,"family":"PB-MATRIX-0","focused_test":"packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0a.py","future_family_selection_granted":false,"hidden_test_access_rejected":true,"implementation_package":"packages/adeu_benchmarking","matrix_controls_non_ranking":true,"merged_at":"2026-05-09T01:38:31Z","merged_pr":"#488","model_ranking_authority_granted":false,"official_programbench_authority_granted":false,"reference_fixture_root":"apps/api/fixtures/benchmarking/vnext_plus260","schema":"pb_matrix_0a_matrix_intake_closeout_evidence@1","selected_record_shapes":["programbench_local_case_matrix_request@1","programbench_local_case_inclusion_manifest@1","programbench_local_case_lineage_eligibility_review@1","programbench_local_case_matrix_control_contract@1","programbench_local_case_matrix_non_authority_guardrail@1"],"verification_commands":[".venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0a.py -q","make check","make arc-closeout-check ARC=260"]}
```

## Recommendation

- gate decision:
  - `PB_MATRIX_0A_MATRIX_INTAKE_COMPLETE_ON_MAIN`
- rationale:
  - `v260` closes the bounded `PB-MATRIX-0-A` case-matrix intake seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - five local cleanroom case-matrix intake record surfaces
    - released local trial and optional retry lineage required before case
      inclusion
    - row-shaped case candidates with explicit lineage refs and boundary
      hashes
    - eligibility rows must cover every candidate case
    - aggregate counts remain local inventory/accounting only
    - multi-profile or multi-control matrices require comparability-only
      non-ranking posture
    - forbidden action and non-authority rows cannot duplicate kind keys
    - no result projection, observation ledger, coverage register,
      contamination register, matrix summary, benchmark score, model ranking,
      batch execution, official ProgramBench participation, hidden-test
      handling, second retry authority, or future-family selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- next bounded slice:
  - `PB-MATRIX-0-B`
