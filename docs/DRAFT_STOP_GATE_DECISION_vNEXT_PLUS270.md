# Draft Stop-Gate Decision vNext+270

Status: post-closeout decision for `PB-SINGLE-CASE-RUN-0-B`.

Authority layer: closeout / implementation evidence.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS270.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+270` /
  `PB-SINGLE-CASE-RUN-0-B` only.
- It closes the one local worker dispatch specimen, execution trace, local
  probe observation bundle, candidate artifact capture, and lifecycle
  projection seam on `main`.
- It does not authorize official ProgramBench participation, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, pass rate,
  solve rate, success rate, baseline comparison, model ranking, leaderboard
  standing, official submission authority, retry authority, batch execution,
  local outcome audit, observation summary, remand or acceptance decision,
  future-family selection, product authorization, graph-memory authority,
  release authority, or recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#498` / `[codex] Implement PB-SINGLE-CASE-RUN-0-B`
- merge evidence:
  - merge commit: `a3bd1649ef47e4341d7e4dc95e5c31560462ee52`
  - merged at: `2026-05-09T23:47:20Z`
  - implementation commits:
    - `4baa8e68e05a6b8a482ee771f077128d192a4b55`
    - `ab87bb82ca09712b410a934f808dd4c76f67fea1`
- released slice A closeout:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md`
- B starter lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS270.md`
- B edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS270_EDGES.md`
- implementation package:
  - `packages/adeu_benchmarking`
- reference fixtures:
  - `apps/api/fixtures/benchmarking/vnext_plus270/`
- focused test:
  - `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0b.py`
- closeout artifacts:
  - `artifacts/quality_dashboard_v270_closeout.json`
  - `artifacts/stop_gate/metrics_v270_closeout.json`
  - `artifacts/stop_gate/report_v270_closeout.md`
- evidence inputs:
  - `artifacts/agent_harness/v270/evidence_inputs/metric_key_continuity_assertion_v270.json`
  - `artifacts/agent_harness/v270/evidence_inputs/runtime_observability_comparison_v270.json`
  - `artifacts/agent_harness/v270/evidence_inputs/pb_single_case_run_0b_closeout_evidence_v270.json`
- runtime event stream:
  - `artifacts/agent_harness/v270/runtime/evidence/local/urm_events.ndjson`

## Exit Criteria

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| Slice B merged on `main` | required | `passed` | PR `#498`; merge commit `a3bd1649ef47e4341d7e4dc95e5c31560462ee52` |
| Selected B record shapes shipped | required | `passed` | dispatch specimen, execution trace, probe observation bundle, candidate artifact capture, lifecycle projection schemas and fixtures |
| B consumes released A refs | required | `passed` | B validator requires released A request, target, preflight, control, and guardrail refs |
| A preflight is not dispatch authority | required | `passed` | B requires B-slice dispatch authority and rejects A-only dispatch |
| Exactly one dispatch specimen exists | required | `passed` | `dispatch_specimen_index = 1`; duplicate dispatch rejected |
| Command rows are argv-shaped | required | `passed` | raw shell strings rejected; shell path basenames and shell control markers rejected |
| Sandbox witnesses are bound | required | `passed` | sandbox instance, attestation, network, Docker, secret, source lookup, decompilation, and write-scope witnesses required |
| Candidate artifact capture is screened | required | `passed` | forbidden-content screen must pass before capture validates |
| Candidate artifact hashes are consistent | required | `passed` | generated artifact rows must match declared hash rows |
| Candidate artifacts stay inside write scope | required | `passed` | capture validator enforces released write-scope posture |
| Lifecycle projection is not benchmark truth | required | `passed` | projection posture blocks new truth and hidden-test equivalence |
| C outcome surfaces stay deferred | required | `passed` | local outcome audit, observation summary, remand/acceptance, and handoff remain unimplemented here |
| Official ProgramBench and benchmark scoring stay absent | required | `passed` | guardrails and reject fixtures enforce non-authority posture |
| Stop-gate metric key continuity | exact keyset equality with v269 | `passed` | 28 / 28 keys match |
| Runtime observability | no regression required | `passed` | elapsed `66 ms`, delta `-32 ms` from v269 |
| Closeout bundle lint | required | `pending until final local run` | `make arc-closeout-check ARC=270` |

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v269_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v270_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+269","baseline_elapsed_ms":98,"baseline_source":"artifacts/stop_gate/report_v269_closeout.md","current_arc":"vNext+270","current_elapsed_ms":66,"current_source":"artifacts/stop_gate/report_v270_closeout.md","delta_ms":-32,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{
  "schema": "pb_single_case_run_0b_closeout_evidence@1",
  "arc": "vNext+270",
  "family": "PB-SINGLE-CASE-RUN-0",
  "closed_slice": "PB-SINGLE-CASE-RUN-0-B",
  "merged_pr": "#498",
  "merge_commit": "a3bd1649ef47e4341d7e4dc95e5c31560462ee52",
  "dispatch_authority_requires_b_lock": true,
  "exactly_one_dispatch_specimen_enforced": true,
  "argv_shaped_command_rows_required": true,
  "raw_shell_strings_rejected": true,
  "shell_path_basename_rejected": true,
  "candidate_artifact_capture_requires_passed_screening": true,
  "candidate_artifact_hash_consistency_enforced": true,
  "lifecycle_projection_not_new_truth": true,
  "benchmark_truth_authority_granted": false
}
```

## Recommendation

- gate decision:
  - `PB_SINGLE_CASE_RUN_0B_LOCAL_SPECIMEN_CAPTURE_COMPLETE_ON_MAIN`
- rationale:
  - `PB-SINGLE-CASE-RUN-0-B` now records one local execution specimen under
    released A controls plus B-slice dispatch authority;
  - command capture is argv-shaped, sandbox/tool/write-scope witnesses are
    bound, candidate artifact capture is gated by passed screening and hash
    consistency, and lifecycle projection remains non-authoritative as
    benchmark truth;
  - proceed to `PB-SINGLE-CASE-RUN-0-C` for local outcome audit,
    observation summary, remand/acceptance decision, pressure-only handoff,
    and family closeout.
