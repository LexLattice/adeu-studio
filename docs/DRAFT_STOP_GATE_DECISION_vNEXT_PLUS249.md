# Draft Stop-Gate Decision vNext+249

Status: post-closeout decision for `PB-RECON-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS249.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+249` / `PB-RECON-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS249.md`.
- It does not authorize equivalence audit, local accepted status, result
  summary, handoff, family closeout alignment, official ProgramBench
  participation, official task execution, official runner integration,
  official evaluator integration, hidden-test handling, hidden-test
  inference, hidden-test equivalence, original source lookup, decompilation,
  internet lookup inside ProgramBench tasks, external repository lookup,
  benchmark submission, benchmark scoring, benchmark truth, model ranking,
  generated official submissions, unbounded command execution, target
  mutation outside the released sandbox, runtime transition, product
  authorization, graph-memory authority, recursive policy amendment, or
  future-family selection.

## Evidence Source

- merged implementation PR:
  - `#477` (`Implement PB-RECON-0-B local evidence capture`)
- arc-completion merge commit:
  - `1493e44993d8911817ada6b02cd8122730abf5f7`
- merged-at timestamp:
  - `2026-05-08T02:00:50Z`
- implementation commits integrated by the merge:
  - `950ffb487a79b815d21aa14a2039becc0b72b12f`
    (`Implement PB-RECON-0-B local evidence capture`)
  - `7a16e704494022b5eeef69e4aa0dd7fe94bc2287`
    (`Harden PB-RECON-0-B local evidence validation`)
- implementation verification recorded before merge:
  - focused `PB-RECON-0-B` pytest
  - focused `PB-RECON-0-A/B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=249`
  - `make arc-start-check ARC=250`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v249_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v249_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v249_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v249/evidence_inputs/metric_key_continuity_assertion_v249.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v249/evidence_inputs/runtime_observability_comparison_v249.json`
  - `PB-RECON-0-B` local-evidence closeout evidence input:
    `artifacts/agent_harness/v249/evidence_inputs/pb_recon_0b_local_evidence_closeout_evidence_v249.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v249/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS249_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-RECON-0-B` merged on `main` | required | `pass` | PR `#477`, merge commit `1493e44993d8911817ada6b02cd8122730abf5f7` |
| Implementation stayed in the cleanroom reconstruction lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-RECON-0-B` surfaces shipped | required | `pass` | candidate artifact manifest, local run trace, probe result log, and remand/correction record shapes shipped |
| Released `PB-RECON-0-A` substrate is required | required | `pass` | B bundle validation consumes work order, worker context, exclusion manifest, sandbox policy, run budget, and guardrail refs |
| Candidate artifacts remain local workbench artifacts | required | `pass` | manifests reject official submission authority and official ProgramBench posture |
| Generated artifact hashes are unambiguous | required | `pass` | duplicate hash rows for the same generated file are rejected |
| Candidate artifact write scopes bind to sandbox policy | required | `pass` | manifest `write_scope_ref` values are checked against released sandbox `allowed_write_scope_refs` |
| Local run traces are sandbox and budget bound | required | `pass` | traces require released sandbox/run-budget refs plus command allowlist, sandbox, network, secret, and write-scope attestations |
| Local commands are argv-shaped and deterministic | required | `pass` | command argv rows require ordered contiguous `arg_index` values and executable first row |
| Output and filesystem evidence stay bounded | required | `pass` | stdout/stderr hashes plus bounded excerpts; pre/post filesystem manifests and diff refs |
| Sandbox violations cannot be treated as passed probes | required | `pass` | passed probe rows with sandbox violations are rejected |
| Probe result logs stay local | required | `pass` | benchmark truth, hidden-test equivalence, and official evaluator result claims are absent/rejected |
| Remand sources stay cleanroom-local | required | `pass` | hidden-test, official evaluator, original-source, and decompilation remands are not admitted |
| No-correction remands are representable without invented correction rows | required | `pass` | `remand_recorded_no_correction` may carry empty correction attempts while corrected reprobe still requires attempts |
| Released case packet is not mutated by remand | required | `pass` | case-packet mutation posture is fail-closed |
| Deferred `PB-RECON-0-C` surfaces stay deferred | required | `pass` | no equivalence audit, result summary, handoff, family closeout, local accepted status, benchmark score, or model ranking shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v249_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v249/evidence_inputs/metric_key_continuity_assertion_v249.json` records exact keyset equality versus `v248` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v249/evidence_inputs/runtime_observability_comparison_v249.json` records `64 ms` baseline, `66 ms` current, `+2 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v249_closeout_stop_gate_summary@1",
  "arc": "vNext+249",
  "target_path": "PB-RECON-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v248": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 66,
  "runtime_observability_delta_ms": 2
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v248_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v249_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+248","baseline_elapsed_ms":64,"baseline_source":"artifacts/stop_gate/report_v248_closeout.md","current_arc":"vNext+249","current_elapsed_ms":66,"current_source":"artifacts/stop_gate/report_v249_closeout.md","delta_ms":2,"schema":"runtime_observability_comparison@1"}
```

## Recommendation

- gate decision:
  - `PB_RECON_0B_LOCAL_EVIDENCE_CAPTURE_COMPLETE_ON_MAIN`
- rationale:
  - `v249` closes the bounded `PB-RECON-0-B` local-evidence capture seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - four cleanroom reconstruction local-evidence record surfaces
    - released `PB-RECON-0-A` work order, worker context, exclusion manifest,
      sandbox policy, run budget, and guardrail refs required
    - candidate artifacts remain local workbench artifacts, not official
      submissions
    - generated files are hash-bound exactly once and write-scope-bound to
      the released sandbox policy
    - local run traces require command allowlist matches and sandbox,
      network, secret-absence, and write-scope attestations
    - stdout/stderr and filesystem evidence stay bounded and replayable
    - sandbox violations cannot become passed local evidence
    - remand/correction records remain local-cleanroom-evidence only and can
      represent no-correction remands without inventing correction rows
    - no equivalence audit, result summary, local accepted status, handoff,
      family closeout, official ProgramBench runner/evaluator integration,
      hidden-test handling, benchmark truth, benchmark score, model ranking,
      official submission authority, runtime transition, product authority,
      graph-memory authority, recursive-policy amendment, or future-family
      selection shipped
  - stop-gate schema-family and metric-key continuity stayed intact;
  - runtime observability remained informational-only;
  - `PB-RECON-0` remains open for `PB-RECON-0-C`, which requires its own
    canonical starter lock.
