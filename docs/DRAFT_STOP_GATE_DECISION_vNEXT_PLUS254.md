# Draft Stop-Gate Decision vNext+254

Status: post-closeout decision for `PB-TRIAL-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS254.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+254` / `PB-TRIAL-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS254.md`.
- It does not authorize worker dispatch, command execution, candidate
  artifact snapshotting, local trial execution capture, lifecycle projection,
  local outcome audit, trial observation summary, remand decision, retry
  dispatch authority, official ProgramBench participation, official task
  execution, official runner integration, official evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, generated official submissions, official
  submission authority, unbounded command execution, target mutation outside
  released local artifacts, runtime transition, product authorization,
  graph-memory authority, recursive policy amendment, or future-family
  selection.

## Evidence Source

- merged implementation PR:
  - `#482` (`Implement PB-TRIAL-0-A trial preflight`)
- arc-completion merge commit:
  - `cfff8e3ea378b3236362882df41e0a11db51cf73`
- merged-at timestamp:
  - `2026-05-08T18:00:36Z`
- implementation commits integrated by the merge:
  - `e4ca5038b424c76bfe77a2aaf4284140e1c05080`
    (`Implement PB-TRIAL-0-A trial preflight`)
  - `d205660a85c4145731b39346edb510aed2e28ddb`
    (`Address PB-TRIAL-0-A review gates`)
- implementation verification recorded before merge:
  - focused `PB-TRIAL-0-A` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=254`
  - `make arc-start-check ARC=255`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v254_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v254_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v254_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v254/evidence_inputs/metric_key_continuity_assertion_v254.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v254/evidence_inputs/runtime_observability_comparison_v254.json`
  - `PB-TRIAL-0-A` trial-preflight closeout evidence input:
    `artifacts/agent_harness/v254/evidence_inputs/pb_trial_0a_trial_preflight_closeout_evidence_v254.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v254/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS254_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-TRIAL-0-A` merged on `main` | required | `pass` | PR `#482`, merge commit `cfff8e3ea378b3236362882df41e0a11db51cf73` |
| Implementation stayed in the local cleanroom trial lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-TRIAL-0-A` surfaces shipped | required | `pass` | trial docket, execution runbook, sandbox readiness review, and non-authority guardrail shapes shipped |
| Released `PB-ATTEMPT-0` substrate is required | required | `pass` | bundle validation consumes attempt request, worker input packet, dispatch preflight, attempt guardrail, result-review context, and family closeout refs |
| Prior attempt result review remains context only | required | `pass` | trial docket uses `prior_attempt_result_review_context_ref`; validation rejects mismatched attempt result-review context |
| Attempt result context is retry-compatible | required | `pass` | only remand-required or inconclusive attempt contexts can pass; contamination, sandbox/export-blocked, accepted, and future-only contexts are rejected |
| Trial docket cardinality is bounded | required | `pass` | docket requires `single_trial_only` and one attempt lifecycle package |
| Runbook is replayable and non-dispatching | required | `pass` | runbook carries input/context/runbook hashes, materialization policy, sandbox/budget refs, witness requirements, and no dispatch/execution authority |
| Nested runbook rows are deterministic | required | `pass` | allowed-step, forbidden-step, and capture-obligation refs must be sorted and unique |
| Sandbox readiness is row-backed | required | `pass` | readiness rows cover network, source lookup, decompilation, Docker socket, host secrets, write scope, tool manifest, and run budget |
| Readiness maps to later witness requirements | required | `pass` | readiness witness refs must match the runbook witness requirement refs |
| Non-closed tool manifest cannot be ready | required | `pass` | ready readiness requires closed tool manifest posture |
| A does not emit B/C artifacts | required | `pass` | no dispatch record, execution capture, candidate snapshot, lifecycle projection, outcome audit, observation summary, remand decision, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, retry authority, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v254_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v254/evidence_inputs/metric_key_continuity_assertion_v254.json` records exact keyset equality versus `v253` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v254/evidence_inputs/runtime_observability_comparison_v254.json` records `72 ms` baseline, `72 ms` current, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v254_closeout_stop_gate_summary@1",
  "arc": "vNext+254",
  "target_path": "PB-TRIAL-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v253": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 72,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v253_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v254_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+253","baseline_elapsed_ms":72,"baseline_source":"artifacts/stop_gate/report_v253_closeout.md","current_arc":"vNext+254","current_elapsed_ms":72,"current_source":"artifacts/stop_gate/report_v254_closeout.md","delta_ms":0,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_TRIAL_0A_TRIAL_PREFLIGHT_COMPLETE_ON_MAIN`
- rationale:
  - `v254` closes the bounded `PB-TRIAL-0-A` trial-preflight seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four local cleanroom trial-preflight record surfaces
    - released `PB-ATTEMPT-0` lifecycle rows and family closeout refs required
      before trial bundle validation
    - prior attempt result review is lifecycle context only, not trial outcome
    - contamination/sandbox/export-blocked, accepted, and future-only attempt
      contexts cannot become trial-ready substrate
    - execution runbook remains plan-only and hash-bound
    - sandbox readiness requires row-backed witness requirements and a closed
      tool manifest before a ready posture can exist
    - no worker dispatch, command execution, candidate snapshot, lifecycle
      projection, outcome audit, observation summary, remand decision, retry
      authority, official ProgramBench runner/evaluator integration,
      hidden-test handling, benchmark truth, benchmark score, model ranking,
      official submission authority, runtime transition, product authority,
      graph-memory authority, recursive-policy amendment, or future-family
      selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-TRIAL-0` remains open for `PB-TRIAL-0-B`, which requires its own
    canonical starter lock.
