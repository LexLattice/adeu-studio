# Draft Stop-Gate Decision vNext+264

Status: post-closeout decision for `PB-CASE-EXPANSION-0-B`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS264.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+264` /
  `PB-CASE-EXPANSION-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS264.md`.
- It does not authorize local case lineage registrations, readiness
  summaries, matrix candidate handoffs, family closeout, local case
  execution, probe execution, batch command execution, candidate
  materialization, official ProgramBench participation, official
  runner/evaluator integration, hidden-test handling, hidden-test inference,
  hidden-test equivalence, benchmark scoring, benchmark truth, baseline
  comparison, pass rate, solve rate, success rate, model ranking,
  leaderboard standing, official submission authority, second retry
  authority, retry-chain authority, future-family selection, product
  authorization, graph-memory authority, release authority, or recursive
  policy amendment.

## Evidence Source

- merged implementation PR:
  - `#492` (`Implement PB-CASE-EXPANSION-0-B blueprint slice`)
- arc-completion merge commit:
  - `01b9f9daee005784598bc6c6aabd82bdfb0d23c5`
- merged-at timestamp:
  - `2026-05-09T14:47:21Z`
- implementation commits integrated by the merge:
  - `7b98da7b1e0f5951e36953e1028f12cf06299fb0`
    (`Implement PB-CASE-EXPANSION-0-B blueprint slice`)
  - `a903b246773eb18615115f9c11f79d78d84f2137`
    (`Tighten PB case expansion evidence bindings`)
- implementation verification recorded before merge:
  - focused `PB-CASE-EXPANSION-0-B` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=264`
  - `make arc-start-check ARC=265`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v264_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v264_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v264_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v264/evidence_inputs/metric_key_continuity_assertion_v264.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v264/evidence_inputs/runtime_observability_comparison_v264.json`
  - `PB-CASE-EXPANSION-0-B` closeout evidence input:
    `artifacts/agent_harness/v264/evidence_inputs/pb_case_expansion_0b_closeout_evidence_v264.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v264/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS264_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-CASE-EXPANSION-0-B` merged on `main` | required | `pass` | PR `#492`, merge commit `01b9f9daee005784598bc6c6aabd82bdfb0d23c5` |
| Implementation stayed in the local cleanroom case-expansion lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-CASE-EXPANSION-0-B` surfaces shipped | required | `pass` | blueprint, evidence pack, probe contract, oracle boundary, and contamination screen shapes shipped |
| B consumes released A rows before blueprint validation | required | `pass` | bundle validator requires A request, source pool, eligibility review, control contract, and guardrail refs |
| Blueprints cannot target A-blocked case ideas | required | `pass` | reject fixture covers blocked or unknown candidate blueprint |
| Blueprint sources cannot widen beyond A-allowed sources | required | `pass` | bundle validator checks blueprint source refs against A allowed and candidate source refs |
| Evidence source witnesses are source-identity bound | required | `pass` | evidence pack hashes must match A source identity hashes |
| Behavior obligations require matching basis witnesses | required | `pass` | review hardening requires basis rows to cite witnesses that witness the same obligation |
| Oracle basis witnesses resolve to the evidence pack | required | `pass` | review hardening rejects oracle basis rows backed by foreign witnesses |
| No derived-summary laundering law is enforced | required | `pass` | validators reject hidden/forbidden names, paths, excerpts, test names, semantic summaries, hidden artifact identifiers, original-source clues, and derived facts |
| Probe contracts remain argv-shaped and non-executing | required | `pass` | validators reject raw shell strings and command execution authority |
| Oracle boundary remains local-only | required | `pass` | hidden-test equivalence, official evaluator equivalence, and benchmark truth are rejected |
| Contamination screens fail closed | required | `pass` | clean screen cannot carry hidden, forbidden, evaluator, or source/decompilation exposure refs |
| B does not emit C artifacts | required | `pass` | no lineage registration, readiness summary, matrix handoff, or family closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, baseline comparison, model ranking, batch execution, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v264_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v264/evidence_inputs/metric_key_continuity_assertion_v264.json` records exact keyset equality versus `v263` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v264/evidence_inputs/runtime_observability_comparison_v264.json` records `85 ms` baseline, `85 ms` current, `0 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v264_closeout_stop_gate_summary@1",
  "arc": "vNext+264",
  "target_path": "PB-CASE-EXPANSION-0-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v263": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 85,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v263_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v264_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+263","baseline_elapsed_ms":85,"baseline_source":"artifacts/stop_gate/report_v263_closeout.md","current_arc":"vNext+264","current_elapsed_ms":85,"current_source":"artifacts/stop_gate/report_v264_closeout.md","delta_ms":0,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+264","baseline_comparison_authority_granted":false,"benchmark_truth_authority_granted":false,"case_lineage_registration_authority_granted":false,"clean_contamination_screen_required":true,"closed_slice":"PB-CASE-EXPANSION-0-B","execution_authority_granted":false,"family":"PB-CASE-EXPANSION-0","focused_test":"packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0b.py","future_family_selection_granted":false,"hidden_test_equivalence_rejected":true,"implementation_package":"packages/adeu_benchmarking","merged_at":"2026-05-09T14:47:21Z","merged_pr":"#492","model_ranking_authority_granted":false,"no_derived_summary_laundering_enforced":true,"official_programbench_authority_granted":false,"oracle_basis_witnesses_resolve_to_evidence_pack":true,"probe_contracts_argv_shaped":true,"reference_fixture_root":"apps/api/fixtures/benchmarking/vnext_plus264","schema":"pb_case_expansion_0b_closeout_evidence@1","selected_record_shapes":["programbench_local_case_blueprint@1","programbench_local_case_cleanroom_evidence_pack@1","programbench_local_case_probe_contract@1","programbench_local_case_oracle_boundary@1","programbench_local_case_contamination_screen@1"],"source_witness_basis_obligation_match_required":true,"verification_commands":[".venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0b.py -q","make check","make arc-closeout-check ARC=264"]}
```

## Recommendation

- gate decision:
  - `PB_CASE_EXPANSION_0B_BLUEPRINT_AND_BOUNDARY_COMPLETE_ON_MAIN`
- rationale:
  - `v264` closes the bounded `PB-CASE-EXPANSION-0-B` blueprint,
    cleanroom evidence, probe contract, oracle boundary, and contamination
    screen seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - five local cleanroom case blueprint record surfaces
    - released `PB-CASE-EXPANSION-0-A` rows required before B validation
    - A-blocked case ideas cannot be blueprinted
    - blueprint source refs cannot widen the A source boundary
    - behavior obligations bind to matching source witnesses and basis rows
    - oracle basis witnesses resolve against the cleanroom evidence pack
    - no-derived-summary laundering is rejected
    - probe contracts are argv-shaped, plan-only, and non-executing
    - local oracle boundaries do not claim hidden-test equivalence,
      evaluator equivalence, or benchmark truth
    - contamination screens fail closed
    - no lineage registration, readiness summary, matrix handoff, family
      closeout, local execution, batch execution, benchmark score, baseline
      comparison, model ranking, official ProgramBench participation, or
      future-family selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- next bounded slice:
  - `PB-CASE-EXPANSION-0-C`
