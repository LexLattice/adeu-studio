# Draft Stop-Gate Decision vNext+258

Status: post-closeout decision for `PB-RETRY-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS258.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+258` / `PB-RETRY-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md`.
- It does not authorize retry outcome audit, same-lineage delta summary,
  remand settlement, second retry authority, official ProgramBench
  participation, hidden-test handling, hidden-test inference, benchmark
  scoring, benchmark truth, model ranking, official submission authority,
  future-family selection, product authorization, graph-memory authority, or
  recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#486` (`Implement PB-RETRY-0-B retry dispatch specimen`)
- arc-completion merge commit:
  - `15cc6a6dc13e323842854bbe4d619c5f339a5f4f`
- merged-at timestamp:
  - `2026-05-09T00:02:32Z`
- implementation commits integrated by the merge:
  - `02694c7` (`Implement PB-RETRY-0-B retry dispatch specimen`)
  - `efaa8ef` (`Harden PB-RETRY-0-B dispatch bindings`)
- implementation verification recorded before merge:
  - focused `PB-RETRY-0-B` pytest
  - `make lint`
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=258`
  - `make arc-start-check ARC=259`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v258_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v258_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v258_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v258/evidence_inputs/metric_key_continuity_assertion_v258.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v258/evidence_inputs/runtime_observability_comparison_v258.json`
  - `PB-RETRY-0-B` dispatch-specimen closeout evidence input:
    `artifacts/agent_harness/v258/evidence_inputs/pb_retry_0b_dispatch_specimen_closeout_evidence_v258.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v258/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS258_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-RETRY-0-B` merged on `main` | required | `pass` | PR `#486`, merge commit `15cc6a6dc13e323842854bbe4d619c5f339a5f4f` |
| Implementation stayed in the local cleanroom retry lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-RETRY-0-B` surfaces shipped | required | `pass` | dispatch, execution capture, candidate delta, lifecycle projection, and sandbox trace shapes shipped |
| Released A retry substrate is required | required | `pass` | bundle validation consumes request, lineage registry, remand source index, eligibility review, scope contract, and guardrail refs |
| A eligibility is bound to the same request | required | `pass` | review hardening rejects stale eligibility, registry, scope, or guardrail refs |
| Dispatch authority is B-lock-bound | required | `pass` | validation rejects missing/stale dispatch authority refs |
| Retry cardinality is bounded | required | `pass` | dispatch rows require one retry specimen and `retry_depth = 1` |
| Retry dispatch preserves source trial boundary | required | `pass` | review hardening rejects worker input/context/tool/materialization hash drift from source trial dispatch |
| Retry dispatch preserves A cleanroom scope | required | `pass` | validation binds retry scope delta and sandbox policy hashes to released A scope |
| Execution capture is local and screened | required | `pass` | stdout/stderr/transcript hashes, bounded excerpts, timeout, tool-call manifest, screening basis refs, and screened output hashes are required |
| Candidate delta snapshot is screened before materialization | required | `pass` | validation blocks snapshots unless forbidden-content screening passes and materialization input matches screened output hash |
| Candidate delta remains inside released write scope | required | `pass` | validation binds retry delta write scope to source trial snapshot write scope |
| Lifecycle projection does not define new evidence law | required | `pass` | validation rejects `new_evidence_law_posture` drift |
| Sandbox trace is witnessed and clean | required | `pass` | trace requires network, Docker socket, host secret, source lookup, decompilation, write scope, resource, and tool-manifest witness refs and rejects violation refs |
| B does not emit C artifacts | required | `pass` | no outcome audit, delta summary, remand settlement, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, official submission, or second retry authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v258_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v258/evidence_inputs/metric_key_continuity_assertion_v258.json` records exact keyset equality versus `v257` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v258/evidence_inputs/runtime_observability_comparison_v258.json` records `103 ms` baseline, `104 ms` current, `1 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v258_closeout_stop_gate_summary@1",
  "arc": "vNext+258",
  "target_path": "PB-RETRY-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v257": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 104,
  "runtime_observability_delta_ms": 1
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v257_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v258_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+257","baseline_elapsed_ms":103,"baseline_source":"artifacts/stop_gate/report_v257_closeout.md","current_arc":"vNext+258","current_elapsed_ms":104,"current_source":"artifacts/stop_gate/report_v258_closeout.md","delta_ms":1,"schema":"runtime_observability_comparison@1"}
```

## Decision

`PB-RETRY-0-B` is closed on `main`. Continue to `PB-RETRY-0-C` for retry
outcome audit, same-lineage delta observation summary, remand settlement, and
family closeout alignment.
