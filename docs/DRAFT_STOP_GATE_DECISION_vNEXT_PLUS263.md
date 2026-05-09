# Draft Stop-Gate Decision vNext+263

Status: post-closeout decision for `PB-CASE-EXPANSION-0-A`.

Authority layer: closeout evidence on `main`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS263.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "required_in_closeout": true,
  "all_passed": true
}
```

## Decision Guardrail

- This closeout decision is scoped to `vNext+263` /
  `PB-CASE-EXPANSION-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS263.md`.
- It does not authorize case blueprints, cleanroom evidence packs, probe
  contracts, oracle boundaries, contamination screens, lineage registrations,
  readiness summaries, matrix candidate handoffs, family closeout, local case
  execution, batch command execution, candidate materialization, official
  ProgramBench participation, official runner/evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  benchmark scoring, benchmark truth, baseline comparison, pass rate, solve
  rate, success rate, model ranking, leaderboard standing, official
  submission authority, second retry authority, retry-chain authority,
  future-family selection, product authorization, graph-memory authority,
  release authority, or recursive policy amendment.

## Evidence Source

- merged implementation PR:
  - `#491` (`Implement PB-CASE-EXPANSION-0-A`)
- arc-completion merge commit:
  - `05b201900a3a40ae68496ca87b586e954d27775b`
- merged-at timestamp:
  - `2026-05-09T12:45:45Z`
- implementation commits integrated by the merge:
  - `e9d917e5fb2e437c7f53e860e98cb6514567b348`
    (`Implement PB-CASE-EXPANSION-0-A`)
  - `5e04ee3b0e5328b2999136a16b71f6bd9a629a66`
    (`Address PB-CASE-EXPANSION-0-A review comments`)
  - `af9e3a24c6d031e42c4228f2281d6acab82b961d`
    (`Address PB-CASE-EXPANSION-0-A Gemini comments`)
- implementation verification recorded before merge:
  - focused `PB-CASE-EXPANSION-0-A` pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=263`
  - `make arc-start-check ARC=264`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v263_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v263_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v263_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v263/evidence_inputs/metric_key_continuity_assertion_v263.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v263/evidence_inputs/runtime_observability_comparison_v263.json`
  - `PB-CASE-EXPANSION-0-A` closeout evidence input:
    `artifacts/agent_harness/v263/evidence_inputs/pb_case_expansion_0a_closeout_evidence_v263.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v263/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS263_EDGES.md`

## Exit-Criteria Check

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `PB-CASE-EXPANSION-0-A` merged on `main` | required | `pass` | PR `#491`, merge commit `05b201900a3a40ae68496ca87b586e954d27775b` |
| Implementation stayed in the local cleanroom case-expansion lane | required | `pass` | merged implementation package is `adeu_benchmarking` |
| Selected `PB-CASE-EXPANSION-0-A` surfaces shipped | required | `pass` | expansion request, source pool manifest, eligibility review, control contract, and non-authority guardrail shapes shipped |
| A consumes released `PB-MATRIX-0` lineage before matrix-driven pressure | required | `pass` | validators require released matrix closeout refs for matrix pressure |
| Selection and dedupe posture is explicit | required | `pass` | request and candidate rows carry selection horizon, rationale, bias, diversity, dedupe, subset hashes, overlap refs, and non-representative posture |
| Duplicate local case ideas cannot launder as new supply | required | `pass` | validators reject duplicates without explicit smoke/regression rationale |
| Source pool rows are hash-bound and concrete | required | `pass` | source rows require concrete refs and identity hashes; globs do not become source refs |
| Forbidden or hidden sources cannot be allowed expansion evidence | required | `pass` | validators check both source kind and source origin posture, and forbid visible posture for forbidden rows |
| No derived-summary laundering law is enforced | required | `pass` | validators reject hidden/forbidden names, paths, excerpts, test names, semantic summaries, hidden artifact identifiers, original-source clues, and derived facts in visible rows |
| Support-only context cannot create eligibility alone | required | `pass` | eligible candidate case ideas require cleanroom-visible source witnesses |
| Manifest summary refs match source row states | required | `pass` | forbidden, blocked, auditor-only, and support-only summary refs must exactly match row classifications |
| Eligibility warnings and blockers resolve to row evidence | required | `pass` | carried blockers and warnings must resolve to candidate eligibility row refs |
| A does not emit B/C artifacts | required | `pass` | no blueprint, evidence pack, probe contract, oracle boundary, contamination screen, lineage registration, readiness, handoff, or closeout shape shipped |
| Official ProgramBench and benchmark truth stay absent | required | `pass` | no official runner/evaluator integration, hidden-test handling, benchmark score, baseline comparison, model ranking, batch execution, or official submission authority shipped |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v263_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v263/evidence_inputs/metric_key_continuity_assertion_v263.json` records exact keyset equality versus `v262` |
| Runtime observability captured | informational | `pass` | `artifacts/agent_harness/v263/evidence_inputs/runtime_observability_comparison_v263.json` records `70 ms` baseline, `85 ms` current, `15 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v263_closeout_stop_gate_summary@1",
  "arc": "vNext+263",
  "target_path": "PB-CASE-EXPANSION-0-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v262": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 85,
  "runtime_observability_delta_ms": 15
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v262_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v263_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+262","baseline_elapsed_ms":70,"baseline_source":"artifacts/stop_gate/report_v262_closeout.md","current_arc":"vNext+263","current_elapsed_ms":85,"current_source":"artifacts/stop_gate/report_v263_closeout.md","delta_ms":15,"schema":"runtime_observability_comparison@1"}
```

## Slice Evidence Input

```json
{"arc":"vNext+263","baseline_comparison_authority_granted":false,"benchmark_truth_authority_granted":false,"blueprint_authority_granted":false,"closed_slice":"PB-CASE-EXPANSION-0-A","dedupe_without_rationale_rejected":true,"family":"PB-CASE-EXPANSION-0","focused_test":"packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0a.py","forbidden_origin_visible_posture_rejected":true,"future_family_selection_granted":false,"implementation_package":"packages/adeu_benchmarking","manifest_summary_refs_exact":true,"merged_at":"2026-05-09T12:45:45Z","merged_pr":"#491","model_ranking_authority_granted":false,"no_derived_summary_laundering_enforced":true,"official_programbench_authority_granted":false,"orphan_carried_warning_rejected":true,"reference_fixture_root":"apps/api/fixtures/benchmarking/vnext_plus263","schema":"pb_case_expansion_0a_closeout_evidence@1","selected_record_shapes":["programbench_local_case_expansion_request@1","programbench_local_case_source_pool_manifest@1","programbench_local_case_expansion_eligibility_review@1","programbench_local_case_expansion_control_contract@1","programbench_local_case_expansion_non_authority_guardrail@1"],"verification_commands":[".venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0a.py -q","make check","make arc-closeout-check ARC=263"]}
```

## Recommendation

- gate decision:
  - `PB_CASE_EXPANSION_0A_INTAKE_AND_SOURCE_POOL_COMPLETE_ON_MAIN`
- rationale:
  - `v263` closes the bounded `PB-CASE-EXPANSION-0-A` request,
    source-pool, eligibility, control, and guardrail seam on `main`;
  - the shipped slice stayed properly bounded:
    - one repo-owned implementation package (`adeu_benchmarking`) only
    - five local cleanroom case-expansion intake record surfaces
    - released `PB-MATRIX-0` lineage required for matrix-driven pressure
    - selection, dedupe, source identity, source visibility, and
      non-representative posture are explicit
    - no-derived-summary laundering is rejected
    - forbidden origin and source kind rows cannot become visible expansion
      evidence
    - support-only context cannot create eligibility alone
    - no blueprint, evidence pack, probe contract, oracle boundary,
      contamination screen, lineage registration, readiness summary, handoff,
      family closeout, local execution, batch execution, benchmark score,
      baseline comparison, model ranking, official ProgramBench participation,
      or future-family selection shipped
  - deterministic closeout artifacts preserve the frozen stop-gate schema and
    exact metric keyset.
- next bounded slice:
  - `PB-CASE-EXPANSION-0-B`
