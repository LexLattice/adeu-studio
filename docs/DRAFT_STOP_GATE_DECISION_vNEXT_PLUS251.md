# Draft Stop-Gate Decision vNext+251

Status: post-closeout decision for `PB-ATTEMPT-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+251` / `PB-ATTEMPT-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS251.md`.
- It does not authorize worker invocation, command execution, candidate
  materialization, local probe execution, workbench evidence export, attempt
  result review, remand queue, official ProgramBench participation, official
  task execution, official runner integration, official evaluator
  integration, hidden-test handling, hidden-test inference, hidden-test
  equivalence, original source lookup, decompilation, internet lookup inside
  ProgramBench tasks, external repository lookup, benchmark submission,
  benchmark scoring, benchmark truth, model ranking, generated official
  submissions, official submission authority, unbounded command execution,
  target mutation outside released local artifacts, runtime transition,
  product authorization, graph-memory authority, recursive policy amendment,
  or future-family selection.

## Evidence Source

- merged implementation PR:
  - `#479` (`Implement PB-ATTEMPT-0-A attempt preflight schemas`)
- arc-completion merge commit:
  - `454d60047afa7d5f840e910a226f015b23cf4f1d`
- merged-at timestamp:
  - `2026-05-08T13:23:44Z`
- implementation commits integrated by the merge:
  - `c500eb9c28c24be5cbddd988da125a0ce3615a19`
    (`Implement PB-ATTEMPT-0-A attempt preflight schemas`)
- implementation verification recorded before merge:
  - focused `PB-ATTEMPT-0-A` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=251`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v251_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v251_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v251_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v251/evidence_inputs/metric_key_continuity_assertion_v251.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v251/evidence_inputs/runtime_observability_comparison_v251.json`
  - `PB-ATTEMPT-0-A` attempt-preflight closeout evidence input:
    `artifacts/agent_harness/v251/evidence_inputs/pb_attempt_0a_attempt_preflight_closeout_evidence_v251.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v251/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS251_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-ATTEMPT-0-A` merged on `main` | required | `pass` | PR `#479`, merge commit `454d60047afa7d5f840e910a226f015b23cf4f1d` |
| Implementation stayed in the cleanroom attempt lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-ATTEMPT-0-A` surfaces shipped | required | `pass` | attempt request, worker input packet, dispatch preflight, and non-authority guardrail shapes shipped |
| Released `PB-RECON-0` substrate is required | required | `pass` | bundle validation consumes released work order, worker context, exclusion manifest, sandbox policy, run budget, result summary, workbench guardrail, and family closeout refs |
| Attempt request result-summary posture is compatible | required | `pass` | local accepted, contamination-blocked, sandbox-violation-blocked, and future-family-only summaries are rejected |
| Worker input stays cleanroom-visible only | required | `pass` | worker-visible refs must stay within released visible/advisory/probe/sandbox/budget refs and cannot intersect auditor-only exclusions |
| Exclusion summaries are non-content-bearing | required | `pass` | source names, source paths, excerpts, semantic summaries, test names, hidden artifact ids, and original-source clues are rejected |
| Worker input packet is replayable | required | `pass` | packet requires manifest hash, visible ref count, and forbidden-ref exposure check hash |
| Context derivation does not leak hidden evidence | required | `pass` | derivation rows may use explicit linkage refs but cannot cite hidden, forbidden, or auditor-only source refs |
| Dispatch preflight is eligibility-only | required | `pass` | preflight requires eligibility-only/no-invocation posture and rejects dispatch/execution authority |
| Sandbox and budget enforcement requirements are explicit | required | `pass` | preflight requires sandbox enforcement and budget enforcement requirement refs |
| A does not emit B/C artifacts | required | `pass` | no invocation, output capture, materialization, sandbox trace, export, result review, remand queue, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v251_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v251/evidence_inputs/metric_key_continuity_assertion_v251.json` records exact keyset equality versus `v250` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v251/evidence_inputs/runtime_observability_comparison_v251.json` records `72 ms` baseline, `72 ms` current, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v251_closeout_stop_gate_summary@1",
  "arc": "vNext+251",
  "target_path": "PB-ATTEMPT-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v250": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 72,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v250_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v251_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+250","baseline_elapsed_ms":72,"baseline_source":"artifacts/stop_gate/report_v250_closeout.md","current_arc":"vNext+251","current_elapsed_ms":72,"current_source":"artifacts/stop_gate/report_v251_closeout.md","delta_ms":0,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_ATTEMPT_0A_ATTEMPT_PREFLIGHT_COMPLETE_ON_MAIN`
- rationale:
  - `v251` closes the bounded `PB-ATTEMPT-0-A` request/input/preflight seam
    on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four cleanroom reconstruction attempt-preflight record surfaces
    - released `PB-RECON-0` workbench rows and family closeout rows required
      before attempt validation
    - worker input packets cannot expose auditor-only, hidden, forbidden,
      postmortem-only, original-source, decompilation, internet, external
      repository, host-secret, or Docker-socket refs
    - exclusion summaries remain category/count/reason/posture/non-exposure
      ledgers and cannot carry source-identifying or content-bearing facts
    - dispatch preflight remains eligibility review only and cannot dispatch
      a worker, execute commands, run probes, or materialize candidate files
    - sandbox and budget enforcement requirements are required before a
      passed preflight can exist
    - no official ProgramBench runner/evaluator integration, hidden-test
      handling, benchmark truth, benchmark score, model ranking, official
      submission authority, runtime transition, product authority,
      graph-memory authority, recursive-policy amendment, or future-family
      selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-ATTEMPT-0-B` remains the next selected pressure inside the already
    selected family, requiring its own canonical starter lock.
