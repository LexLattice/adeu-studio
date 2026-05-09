# Draft Stop-Gate Decision vNext+269

Status: post-closeout decision for `PB-SINGLE-CASE-RUN-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+269` /
  `PB-SINGLE-CASE-RUN-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS269.md`.
- It closes the bounded single-case run request, target selection, execution
  preflight, run control contract, and non-authority guardrail seam.
- It does not authorize worker dispatch, command execution, probe execution,
  candidate artifact capture, lifecycle projection, local outcome audit,
  remand or acceptance decision, retry authority, batch execution, official
  ProgramBench participation, official runner/evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  benchmark scoring, benchmark truth, pass rate, solve rate, success rate,
  baseline comparison, model ranking, leaderboard standing, official
  submission authority, retry-chain authority, future-family selection,
  product authorization, graph-memory authority, release authority, or
  recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#497` (`[codex] Implement PB-SINGLE-CASE-RUN-0-A`)
- merge commit:
  - `67e264aef3c80cc1544e4874f322d3e33b155ebd`
- merged-at timestamp:
  - `2026-05-09T23:14:51Z`
- implementation commits integrated by the merge:
  - `bfbfdd220198508cc46438e1578866b67fd01666`
    (`Implement PB-SINGLE-CASE-RUN-0-A`)
  - `c2d98f370bd6f9342d793368266e72bc910b9d28`
    (`Harden PB single-case run preflight validation`)
- implementation verification recorded before merge:
  - focused `PB-SINGLE-CASE-RUN-0-A` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=269`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v269_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v269_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v269_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v269/evidence_inputs/metric_key_continuity_assertion_v269.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v269/evidence_inputs/runtime_observability_comparison_v269.json`
  - `PB-SINGLE-CASE-RUN-0-A` closeout evidence input:
    `artifacts/agent_harness/v269/evidence_inputs/pb_single_case_run_0a_closeout_evidence_v269.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v269/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS269_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-SINGLE-CASE-RUN-0-A` merged on `main` | required | `pass` | PR `#497`, merge commit `67e264aef3c80cc1544e4874f322d3e33b155ebd` |
| Implementation stayed in the single-case-run lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected A surfaces shipped | required | `pass` | run request, target selection, execution preflight, run control contract, and non-authority guardrail shapes shipped |
| Target route is explicit and bounded | required | `pass` | default route is `matrix_member`; non-matrix routes require route posture |
| Matrix-member targets must be included | required | `pass` | target selection and bundle validators reject non-included matrix membership |
| Blocked target selections cannot bind to ready preflight | required | `pass` | review fix rejects blocked target selection and blocker refs in the bundle |
| Preflight remains eligibility-only | required | `pass` | `preflight_scope_posture = eligibility_review_only_no_dispatch` |
| B witness requirements are declared, not satisfied in A | required | `pass` | witness refs are required fields; A records no sandbox instance or runtime witness satisfaction |
| Ready preflight covers all required checks | required | `pass` | review fix requires the complete required check-kind set and rejects duplicates |
| Control hashes bind target and preflight | required | `pass` | bundle validator binds worker packet, probe basis, runbook, sandbox, budget, tool, and write-scope hashes |
| Guardrail rejects future B/C artifacts | required | `pass` | non-authority guardrail forbids B/C record shapes in A output |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no dispatch, execution, artifact capture, lifecycle projection, scoring, baseline comparison, model ranking, official authority, or future-family selection shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v269_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v269/evidence_inputs/metric_key_continuity_assertion_v269.json` records exact keyset equality versus `v268` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v269/evidence_inputs/runtime_observability_comparison_v269.json` records `117 ms` baseline, `98 ms` current, `-19 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v269_closeout_stop_gate_summary@1",
  "arc": "vNext+269",
  "target_path": "PB-SINGLE-CASE-RUN-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v268": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 98,
  "runtime_observability_delta_ms": -19
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v268_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v269_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+268","baseline_elapsed_ms":117,"baseline_source":"artifacts/stop_gate/report_v268_closeout.md","current_arc":"vNext+269","current_elapsed_ms":98,"current_source":"artifacts/stop_gate/report_v269_closeout.md","delta_ms":-19,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+269","baseline_comparison_authority_granted":false,"batch_execution_authority_granted":false,"benchmark_truth_authority_granted":false,"b_witnesses_declared_not_satisfied":true,"candidate_artifact_capture_granted":false,"closed_slice":"PB-SINGLE-CASE-RUN-0-A","default_target_origin_route":"matrix_member","dispatch_authority_granted":false,"execution_authority_granted":false,"family":"PB-SINGLE-CASE-RUN-0","future_family_selection_granted":false,"implementation_commits":["bfbfdd220198508cc46438e1578866b67fd01666","c2d98f370bd6f9342d793368266e72bc910b9d28"],"implementation_package":"packages/adeu_benchmarking","matrix_member_target_required":true,"merge_commit":"67e264aef3c80cc1544e4874f322d3e33b155ebd","merged_at":"2026-05-09T23:14:51Z","merged_pr":"#497","metric_key_continuity_assertion_path":"artifacts/agent_harness/v269/evidence_inputs/metric_key_continuity_assertion_v269.json","model_ranking_authority_granted":false,"official_programbench_authority_granted":false,"preflight_requires_complete_check_kind_set":true,"preflight_scope_posture":"eligibility_review_only_no_dispatch","reference_fixture_root":"apps/api/fixtures/benchmarking/vnext_plus269","runtime_event_stream_path":"artifacts/agent_harness/v269/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v269/evidence_inputs/runtime_observability_comparison_v269.json","schema":"pb_single_case_run_0a_closeout_evidence@1","selected_record_shapes":["programbench_single_case_run_request@1","programbench_single_case_target_selection@1","programbench_single_case_execution_preflight@1","programbench_single_case_run_control_contract@1","programbench_single_case_run_non_authority_guardrail@1"],"single_case_only_enforced":true,"soft_benchmark_result_language_rejected":true,"target_blocker_refs_rejected_in_bundle":true,"target_selection_must_be_selected_for_preflight":true,"test_reference_path":"packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0a.py","verification_commands":[".venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0a.py -q","make check","make arc-closeout-check ARC=269"]}
```

## Recommendation

- gate decision:
  - `PB_SINGLE_CASE_RUN_0A_REQUEST_TARGET_PREFLIGHT_COMPLETE_ON_MAIN`
- rationale:
  - `v269` closes the bounded `PB-SINGLE-CASE-RUN-0-A` request,
    target-selection, preflight, control-contract, and guardrail seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - five single-case-run A record surfaces
    - matrix-member target selection is the default route
    - blocked or non-included matrix targets cannot bind to a ready preflight
    - ready preflight requires complete check-kind coverage
    - B witness refs are declared but not satisfied in A
    - run control hashes bind the target and preflight basis
    - guardrails forbid B/C artifacts and benchmark-like authority
    - no worker dispatch, command execution, probe execution, artifact
      capture, lifecycle projection, local outcome audit, official
      ProgramBench authority, benchmark scoring, baseline comparison, model
      ranking, batch execution, retry authority, or future-family selection
      shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- family status:
  - `PB-SINGLE-CASE-RUN-0` remains open; proceed to
    `PB-SINGLE-CASE-RUN-0-B`.
