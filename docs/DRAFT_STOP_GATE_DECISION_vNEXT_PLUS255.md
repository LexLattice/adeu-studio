# Draft Stop-Gate Decision vNext+255

Status: post-closeout decision for `PB-TRIAL-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS255.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+255` / `PB-TRIAL-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md`.
- It does not authorize trial outcome audit, observation summary, remand
  decision, retry dispatch authority, official ProgramBench participation,
  official task execution, official runner integration, official evaluator
  integration, hidden-test handling, hidden-test inference, hidden-test
  equivalence, original source lookup, decompilation, internet lookup inside
  ProgramBench tasks, external repository lookup, benchmark submission,
  benchmark scoring, benchmark truth, model ranking, generated official
  submissions, official submission authority, unbounded command execution,
  target mutation outside released local sandbox/write scope, runtime
  transition, product authorization, graph-memory authority, recursive policy
  amendment, or future-family selection.

## Evidence Source

- merged implementation PR:
  - `#483` (`Implement PB-TRIAL-0-B execution specimen records`)
- arc-completion merge commit:
  - `e88b9ab19dfa1130e7799965f6f4761fd76ac94d`
- merged-at timestamp:
  - `2026-05-08T20:09:51Z`
- implementation commits integrated by the merge:
  - `e2777cc` (`Implement PB-TRIAL-0-B execution specimen records`)
  - `3fd60b4` (`Address PB-TRIAL-0-B review feedback`)
- implementation verification recorded before merge:
  - focused `PB-TRIAL-0-B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=255`
  - `make arc-start-check ARC=256`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v255_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v255_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v255_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v255/evidence_inputs/metric_key_continuity_assertion_v255.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v255/evidence_inputs/runtime_observability_comparison_v255.json`
  - `PB-TRIAL-0-B` execution-specimen closeout evidence input:
    `artifacts/agent_harness/v255/evidence_inputs/pb_trial_0b_execution_specimen_closeout_evidence_v255.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v255/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS255_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-TRIAL-0-B` merged on `main` | required | `pass` | PR `#483`, merge commit `e88b9ab19dfa1130e7799965f6f4761fd76ac94d` |
| Implementation stayed in the local cleanroom trial lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-TRIAL-0-B` surfaces shipped | required | `pass` | worker dispatch record, execution capture, candidate artifact snapshot, and lifecycle projection shapes shipped |
| Released `PB-TRIAL-0-A` substrate is required | required | `pass` | bundle validation consumes trial docket, execution runbook, sandbox readiness review, and trial guardrail refs |
| Dispatch requires ready A readiness | required | `pass` | validation rejects blocked A readiness before dispatch rows can validate |
| Dispatch authority is B-lock-bound | required | `pass` | validation rejects missing or stale dispatch authority refs |
| Dispatch cardinality is bounded | required | `pass` | worker dispatch record requires exactly one dispatch specimen per trial docket |
| Dispatch is hash-bound to preflighted input | required | `pass` | dispatch rows bind worker input packet hash, visible context hash, tool manifest refs, sandbox instance, sandbox attestation bundle, and input materialization hash |
| Forbidden access postures are rejected | required | `pass` | validation rejects hidden-test access, source lookup, official runner/evaluator contact, benchmark score, model ranking, official submission, and retry authority posture |
| Execution capture is local and bounded | required | `pass` | transcript/stdout/stderr hashes, bounded excerpts, exit/duration/timeout fields, sandbox witnesses, output capture policy, and worker tool-call manifest are required |
| Candidate snapshot requires clean screening | required | `pass` | validation blocks snapshots unless forbidden-content screening passes |
| Candidate snapshot stays local and scoped | required | `pass` | snapshot must use released write scope, pre/post manifests, fs diff refs, generated file hashes, and `snapshot_inside_write_scope = true` |
| Lifecycle projection maps released attempt lifecycle refs | required | `pass` | review fix requires projection refs to match released `PB-ATTEMPT-0-B` invocation, output capture, materialization, and sandbox trace rows |
| Lifecycle projection does not define new evidence law | required | `pass` | validation rejects `new_evidence_law_posture` drift |
| B does not emit C artifacts | required | `pass` | no outcome audit, observation summary, remand decision, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, retry authority, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v255_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v255/evidence_inputs/metric_key_continuity_assertion_v255.json` records exact keyset equality versus `v254` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v255/evidence_inputs/runtime_observability_comparison_v255.json` records `72 ms` baseline, `72 ms` current, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v255_closeout_stop_gate_summary@1",
  "arc": "vNext+255",
  "target_path": "PB-TRIAL-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v254": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 72,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v254_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v255_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+254","baseline_elapsed_ms":72,"baseline_source":"artifacts/stop_gate/report_v254_closeout.md","current_arc":"vNext+255","current_elapsed_ms":72,"current_source":"artifacts/stop_gate/report_v255_closeout.md","delta_ms":0,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_TRIAL_0B_EXECUTION_SPECIMEN_COMPLETE_ON_MAIN`
- rationale:
  - `v255` closes the bounded `PB-TRIAL-0-B` local-dispatch specimen seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four local cleanroom trial specimen record surfaces
    - released `PB-TRIAL-0-A` docket/runbook/readiness/guardrail refs required
      before trial B bundle validation
    - dispatch stays one specimen per docket and B-lock-bound
    - dispatch and execution capture are hash-bound, sandbox-witnessed, and
      cleanroom-local
    - candidate snapshotting is blocked unless forbidden-content screening
      passes and remains inside released write scope
    - lifecycle projection maps only to released `PB-ATTEMPT-0-B` lifecycle refs
      and cannot define new evidence law
    - no outcome audit, observation summary, remand decision, retry authority,
      official ProgramBench runner/evaluator integration, hidden-test handling,
      benchmark truth, benchmark score, model ranking, official submission
      authority, runtime transition, product authority, graph-memory authority,
      recursive-policy amendment, or future-family selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-TRIAL-0` remains open for `PB-TRIAL-0-C`, which requires its own
    canonical starter lock.
