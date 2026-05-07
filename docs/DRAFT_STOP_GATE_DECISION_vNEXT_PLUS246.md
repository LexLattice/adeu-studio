# Draft Stop-Gate Decision vNext+246

Status: post-closeout decision for `PB-ADAPTER-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS246.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+246` / `PB-ADAPTER-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS246.md`.
- It does not use `PB-ADAPTER-0-B` to authorize `PB-ADAPTER-0-C`,
  reconstruction case packets, readiness summaries, handoffs, family closeout
  alignment, official ProgramBench participation, official task execution,
  official runner integration, hidden-test handling, hidden-test inference,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, generated official submissions, arbitrary
  command execution, target mutation, runtime transition, product
  authorization, graph-memory authority, recursive policy amendment, or
  future-family selection.

## Evidence Source

- merged implementation PR:
  - `#474` (`Implement PB-ADAPTER-0-B probe observation adapter`)
- arc-completion merge commit:
  - `328f0d4e320cdd9b129d81172d7dae53b987b4f5`
- merged-at timestamp:
  - `2026-05-07T23:07:58Z`
- implementation commits integrated by the merge:
  - `1daacac2b7549dd97956de6dd3421d27ec8fe3d8`
    (`Implement PB-ADAPTER-0-B probe adapter`)
  - `9111cec6c6ea48ba4a95cc3dbd98f02329452e62`
    (`Tighten PB-ADAPTER-0-B evidence coverage`)
- implementation verification recorded before merge:
  - focused `PB-ADAPTER-0-B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=246`
  - `make arc-start-check ARC=247`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v246_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v246_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v246_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v246/evidence_inputs/metric_key_continuity_assertion_v246.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v246/evidence_inputs/runtime_observability_comparison_v246.json`
  - `PB-ADAPTER-0-B` probe/observation closeout evidence input:
    `artifacts/agent_harness/v246/evidence_inputs/pb_adapter_0b_probe_observation_closeout_evidence_v246.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v246/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS246_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-ADAPTER-0-B` merged on `main` | required | `pass` | PR `#474`, merge commit `328f0d4e320cdd9b129d81172d7dae53b987b4f5` |
| Implementation stayed in the benchmark cleanroom adapter lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-ADAPTER-0-B` surfaces shipped | required | `pass` | probe plan, observation log, I/O artifact index, and filesystem side-effect record shapes shipped |
| Released `PB-ADAPTER-0-A` substrate is required | required | `pass` | B bundle validator consumes task intake, artifact manifest, visibility manifest, worker access contract, and guardrail refs |
| Probe command shape is constrained | required | `pass` | command rows are argv-shaped unless shell wrapping is explicitly declared with reason; raw shell reject fixture passed |
| Probe observations are normalized | required | `pass` | stdout/stderr hashes, bounded excerpts, exit code, duration, timeout, pre/post manifests, fs diff, and replay limits shipped |
| Hidden evaluator output stays outside inference | required | `pass` | hidden evaluator observation reject fixture passed |
| Local probe evidence stays non-authoritative | required | `pass` | hidden-test equivalence and benchmark-truth reject fixtures passed |
| Filesystem side-effect scope is bounded | required | `pass` | outside-scope side-effect reject fixture passed |
| Observation coverage is exact | required | `pass` | I/O artifact index must cover exactly observations; side-effect rows must cover exactly observations |
| Artifact category overlap is rejected | required | `pass` | cross-category artifact overlap regression passed |
| Deferred `PB-ADAPTER-0-C` surfaces stay deferred | required | `pass` | no case packets, readiness summaries, handoffs, family closeout alignment, official runner integration, benchmark result rows, or generated submissions shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v246_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v246/evidence_inputs/metric_key_continuity_assertion_v246.json` records exact keyset equality versus `v245` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v246/evidence_inputs/runtime_observability_comparison_v246.json` records `75 ms` baseline, `73 ms` current, `-2 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v246_closeout_stop_gate_summary@1",
  "arc": "vNext+246",
  "target_path": "PB-ADAPTER-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v245": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 73,
  "runtime_observability_delta_ms": -2
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v245_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v246_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+245","baseline_elapsed_ms":75,"baseline_source":"artifacts/stop_gate/report_v245_closeout.md","current_arc":"vNext+246","current_elapsed_ms":73,"current_source":"artifacts/stop_gate/report_v246_closeout.md","delta_ms":-2,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_ADAPTER_0B_PROBE_OBSERVATION_ADAPTER_COMPLETE_ON_MAIN`
- rationale:
  - `v246` closes the bounded `PB-ADAPTER-0-B` probe plan and observation
    adapter seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four cleanroom adapter record surfaces
    - released `PB-ADAPTER-0-A` refs required before B evidence can validate
    - argv-shaped command rows by default
    - normalized stdout/stderr/exit/filesystem observation evidence
    - exact I/O and filesystem side-effect observation coverage
    - hidden evaluator, hidden-test equivalence, benchmark truth, official
      probe authority, out-of-scope side effects, and artifact-category
      overlap rejected
    - no reconstruction case packet, readiness summary, handoff, family
      closeout alignment, generated submission, official ProgramBench runner,
      hidden-test handling, benchmark score, model ranking, arbitrary command
      execution, tool invocation, runtime transition, product authority,
      graph-memory authority, recursive-policy amendment, or future-family
      selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-ADAPTER-0` remains open for `PB-ADAPTER-0-C`, which requires its own
    canonical starter lock.
