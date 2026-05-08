# Draft Stop-Gate Decision vNext+257

Status: post-closeout decision for `PB-RETRY-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS257.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+257` / `PB-RETRY-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS257.md`.
- It does not authorize retry dispatch, command execution, retry candidate
  delta snapshotting, local retry execution capture, retry lifecycle
  projection, retry outcome audit, retry delta observation summary, remand
  settlement, second retry authority, multi-attempt comparison, official
  ProgramBench participation, official task execution, official runner
  integration, official evaluator integration, hidden-test handling,
  hidden-test inference, hidden-test equivalence, original source lookup,
  decompilation, internet lookup inside ProgramBench tasks, external
  repository lookup, benchmark submission, benchmark scoring, benchmark truth,
  model ranking, generated official submissions, official submission
  authority, unbounded command execution, target mutation outside released
  local artifacts, runtime transition, product authorization, graph-memory
  authority, recursive policy amendment, or future-family selection.

## Evidence Source

- merged implementation PR:
  - `#485` (`Implement PB-RETRY-0-A retry intake`)
- arc-completion merge commit:
  - `3dd5be6fee20f7aab67a79f25d49e24e8a6d9d3d`
- merged-at timestamp:
  - `2026-05-08T22:57:20Z`
- implementation commits integrated by the merge:
  - `3c85e2b0ff552c6f06c751877b3eacb1dc0e2e21`
    (`Implement PB-RETRY-0-A retry intake`)
  - `cca2ba6512b199d17a8d6ca1eada032a82d007aa`
    (`Harden PB-RETRY-0-A retry eligibility`)
- implementation verification recorded before merge:
  - focused `PB-RETRY-0-A` pytest
  - `make lint`
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=257`
  - `make arc-start-check ARC=258`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v257_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v257_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v257_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v257/evidence_inputs/metric_key_continuity_assertion_v257.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v257/evidence_inputs/runtime_observability_comparison_v257.json`
  - `PB-RETRY-0-A` retry-intake closeout evidence input:
    `artifacts/agent_harness/v257/evidence_inputs/pb_retry_0a_retry_intake_closeout_evidence_v257.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v257/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS257_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-RETRY-0-A` merged on `main` | required | `pass` | PR `#485`, merge commit `3dd5be6fee20f7aab67a79f25d49e24e8a6d9d3d` |
| Implementation stayed in the local cleanroom retry lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-RETRY-0-A` surfaces shipped | required | `pass` | retry request, lineage registry, remand source index, eligibility review, scope contract, and non-authority guardrail shapes shipped |
| Released `PB-TRIAL-0` substrate is required | required | `pass` | bundle validation consumes trial outcome audit, observation summary, remand decision, and family closeout rows |
| Locally accepted trials cannot become retry candidates | required | `pass` | validation rejects `trial_locally_accepted` outcome posture |
| Retry lineage uniqueness is enforced | required | `pass` | lineage registry allows exactly one eligible retry request and rejects existing retry refs |
| Request-side prior retries are rejected | required | `pass` | review fix rejects non-empty `prior_retry_request_refs` in bundle validation |
| Remand source posture matches classification lists | required | `pass` | review fix requires row `retryability_posture` to match retryable, blocked, forbidden, non-retryable, and support-only lists |
| Remand rationale remains local-only | required | `pass` | remand source and rationale rows reject hidden, evaluator, source, decompilation, internet, external repo, benchmark-score, and model-ranking markers |
| Scope contract preserves cleanroom boundary | required | `pass` | unchanged source/tool/sandbox/write/network hashes are required; scope deltas may add only local retry instructions or remand-focused obligations |
| A does not emit B/C artifacts | required | `pass` | no retry dispatch, execution capture, candidate delta snapshot, lifecycle projection, sandbox trace, outcome audit, delta summary, settlement, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, model ranking, retry dispatch, second retry, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v257_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v257/evidence_inputs/metric_key_continuity_assertion_v257.json` records exact keyset equality versus `v256` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v257/evidence_inputs/runtime_observability_comparison_v257.json` records `103 ms` baseline, `103 ms` current, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v257_closeout_stop_gate_summary@1",
  "arc": "vNext+257",
  "target_path": "PB-RETRY-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v256": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 103,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v256_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v257_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+256","baseline_elapsed_ms":103,"baseline_source":"artifacts/stop_gate/report_v256_closeout.md","current_arc":"vNext+257","current_elapsed_ms":103,"current_source":"artifacts/stop_gate/report_v257_closeout.md","delta_ms":0,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_RETRY_0A_RETRY_INTAKE_COMPLETE_ON_MAIN`
- rationale:
  - `v257` closes the bounded `PB-RETRY-0-A` retry-intake seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - six local cleanroom retry intake record surfaces
    - released `PB-TRIAL-0` outcome/remand/closeout refs required before
      retry bundle validation
    - locally accepted trials cannot become retry candidates
    - one eligible retry request per trial remand decision is enforced
    - request-side and registry-side prior retry refs block eligibility
    - remand source list classification must match row retryability posture
    - retry rationale remains local-only and cannot cite hidden/evaluator/source
      evidence or benchmark/model-ranking pressure
    - retry scope preserves unchanged cleanroom boundary hashes
    - no retry dispatch, command execution, candidate delta snapshot,
      retry outcome audit, remand settlement, second retry authority,
      official ProgramBench runner/evaluator integration, hidden-test handling,
      benchmark truth, benchmark score, model ranking, official submission
      authority, runtime transition, product authority, graph-memory authority,
      recursive-policy amendment, or future-family selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-RETRY-0` remains open for `PB-RETRY-0-B`, which requires its own
    canonical starter lock.
