# Draft Stop-Gate Decision vNext+252

Status: post-closeout decision for `PB-ATTEMPT-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+252` / `PB-ATTEMPT-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS252.md`.
- It does not authorize workbench evidence export, attempt result review,
  remand queue, family closeout alignment, official ProgramBench
  participation, official task execution, official runner integration,
  official evaluator integration, hidden-test handling, hidden-test
  inference, hidden-test equivalence, original source lookup, decompilation,
  internet lookup inside ProgramBench tasks, external repository lookup,
  benchmark submission, benchmark scoring, benchmark truth, model ranking,
  generated official submissions, official submission authority, unbounded
  command execution, target mutation outside the released local sandbox/write
  scope, runtime transition, product authorization, graph-memory authority,
  recursive policy amendment, or future-family selection.

## Evidence Source

- merged implementation PR:
  - `#480` (`Implement PB-ATTEMPT-0-B invocation capture`)
- arc-completion merge commit:
  - `2662e608d62a127d061fcaf231408f0f5b6fe615`
- merged-at timestamp:
  - `2026-05-08T14:14:07Z`
- implementation commits integrated by the merge:
  - `a3b40df44b863034343329d80b44f83a198b496c`
    (`Implement PB-ATTEMPT-0-B invocation capture`)
  - `9bba02d86f3d497e6a5c213781c790c14d6cc4e2`
    (`Harden PB-ATTEMPT-0-B output provenance`)
- implementation verification recorded before merge:
  - focused `PB-ATTEMPT-0-B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=252`
  - `make arc-start-check ARC=253`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v252_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v252_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v252_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v252/evidence_inputs/metric_key_continuity_assertion_v252.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v252/evidence_inputs/runtime_observability_comparison_v252.json`
  - `PB-ATTEMPT-0-B` invocation-capture closeout evidence input:
    `artifacts/agent_harness/v252/evidence_inputs/pb_attempt_0b_invocation_capture_closeout_evidence_v252.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v252/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS252_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-ATTEMPT-0-B` merged on `main` | required | `pass` | PR `#480`, merge commit `2662e608d62a127d061fcaf231408f0f5b6fe615` |
| Implementation stayed in the cleanroom attempt lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-ATTEMPT-0-B` surfaces shipped | required | `pass` | worker invocation record, output capture, candidate materialization, and sandbox application trace shapes shipped |
| Released `PB-ATTEMPT-0-A` substrate is required | required | `pass` | B bundle validation consumes attempt request, worker input packet, dispatch preflight, and guardrail refs |
| Blocked preflight cannot produce invocation evidence | required | `pass` | invocation validation requires passed A dispatch preflight |
| Invocation cardinality is bounded | required | `pass` | exactly one worker invocation per attempt request is enforced |
| Invocation stays local and cleanroom-bound | required | `pass` | invocation rows reject hidden-test access, source lookup, internet/decompilation/external-repo access, official runner/evaluator contact, benchmark score, model ranking, and official submission posture |
| Invocation input and tool surfaces are hash-bound | required | `pass` | invocation rows bind input packet hash, worker-visible context hash, tool manifest ref, allowed tool manifest hash, and forbidden tool manifest hash |
| Output capture remains bounded | required | `pass` | output rows require hashes and bounded excerpts for every captured output |
| Forbidden-content screening blocks materialization | required | `pass` | non-passing screening blocks candidate materialization; blocked top-level posture requires matching blocked-row evidence |
| Candidate materialization uses screened output provenance | required | `pass` | materialization input hash must match the screened `worker_declared_candidate_file` output hash |
| Candidate materialization stays local | required | `pass` | materialization requires local-only posture, generated file hashes, output manifest hash, no official submission, no benchmark truth, and `materialized_inside_write_scope = true` |
| Sandbox application trace remains bounded | required | `pass` | traces bind sandbox policy/run budget refs and require network, secret, Docker socket, and source-lookup absence attestations |
| Deferred `PB-ATTEMPT-0-C` surfaces stay deferred | required | `pass` | no workbench evidence export, attempt result review, remand queue, or family closeout alignment shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v252_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v252/evidence_inputs/metric_key_continuity_assertion_v252.json` records exact keyset equality versus `v251` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v252/evidence_inputs/runtime_observability_comparison_v252.json` records `72 ms` baseline, `72 ms` current, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v252_closeout_stop_gate_summary@1",
  "arc": "vNext+252",
  "target_path": "PB-ATTEMPT-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v251": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 72,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v251_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v252_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+251","baseline_elapsed_ms":72,"baseline_source":"artifacts/stop_gate/report_v251_closeout.md","current_arc":"vNext+252","current_elapsed_ms":72,"current_source":"artifacts/stop_gate/report_v252_closeout.md","delta_ms":0,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_ATTEMPT_0B_INVOCATION_CAPTURE_COMPLETE_ON_MAIN`
- rationale:
  - `v252` closes the bounded `PB-ATTEMPT-0-B` invocation-capture seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four cleanroom attempt invocation-capture record surfaces
    - released `PB-ATTEMPT-0-A` attempt request, worker input packet,
      dispatch preflight, and guardrail refs required before B validation
    - blocked preflight cannot be used to create accepted invocation evidence
    - exactly one invocation per attempt request is enforced
    - invocation rows are local-only and reject hidden/source/internet/
      decompilation/external-repo, official runner/evaluator, benchmark
      score, model-ranking, and official submission posture
    - invocation input, visible context, and tool manifests are hash-bound
    - output capture uses hashes plus bounded excerpts
    - candidate materialization requires passed forbidden-content screening
      and matching screened candidate-file output provenance
    - materialization stays inside the released local write scope and cannot
      become official submission or benchmark truth
    - sandbox application traces carry absence attestations for network,
      secrets, Docker socket, and source lookup
    - no workbench evidence export, attempt result review, remand queue,
      family closeout, official ProgramBench runner/evaluator integration,
      hidden-test handling, benchmark truth, benchmark score, model ranking,
      official submission authority, runtime transition, product authority,
      graph-memory authority, recursive-policy amendment, or future-family
      selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-ATTEMPT-0` remains open for `PB-ATTEMPT-0-C`, which requires its own
    canonical starter lock.
