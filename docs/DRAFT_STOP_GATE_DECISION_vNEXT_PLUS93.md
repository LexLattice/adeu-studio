# Draft Stop-Gate Decision (Post vNext+93)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS93.md`

Status: draft decision note (post-hoc closeout capture, March 28, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS93.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v93_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+93` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS93.md`.
- This note captures `V42-E` closeout evidence only; it does not authorize direct online
  submission execution, benchmark-tournament orchestration, API/web operator routes, or
  generalized multi-benchmark/multi-agent widening beyond the bounded
  scorecard/replay/competition-posture seam.
- Canonical `V42-E` release in v93 is carried by the `packages/adeu_arc_agi` and
  `packages/adeu_arc_solver` scorecard surfaces, deterministic fixture replay under
  `apps/api/fixtures/arc_agi/vnext_plus93/`, and the canonical
  `v42e_arc_scorecard_evidence@1` evidence input under
  `artifacts/agent_harness/v93/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `636e543039ff700e3795b2c367fd06bb509a5d20`
- merged implementation PRs:
  - `#315` (`Implement v93 V42-E scorecard manifest baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v93_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v93_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v93_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v93/evidence_inputs/metric_key_continuity_assertion_v93.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v93/evidence_inputs/runtime_observability_comparison_v93.json`
  - `V42-E` scorecard evidence input:
    `artifacts/agent_harness/v93/evidence_inputs/v42e_arc_scorecard_evidence_v93.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v93/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS93_EDGES.md`

## Exit-Criteria Check (vNext+93)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-E` merged with green CI | required | `pass` | PR `#315`, merge commit `636e543039ff700e3795b2c367fd06bb509a5d20` |
| Canonical `adeu_arc_scorecard_manifest@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_scorecard_manifest.v1.json`, `spec/adeu_arc_scorecard_manifest.schema.json` |
| Scorecard source-kind discriminator and authority-posture decomposition are explicit and machine-checkable | required | `pass` | scorecard model validators in `packages/adeu_arc_agi/src/adeu_arc_agi/scorecard.py` and fixture matrix under `apps/api/fixtures/arc_agi/vnext_plus93/` |
| Competition posture is enum-bounded and official posture is fail-closed without valid official authority basis | required | `pass` | `competition_mode_posture` enum checks and `official_imported` enforcement in `scorecard.py` |
| Local replay lineage and external replay authority refs remain explicit and non-conflated | required | `pass` | `local_replay_lineage_refs` and `external_replay_authority_refs` separation checks plus rejected fixture coverage |
| Local-as-official authority laundering is rejected | required | `pass` | rejected fixture `adeu_arc_scorecard_manifest_v93_reject_local_as_official_authority.json` and validator rejection path |
| Leaderboard/competition overclaim from local-only evidence is rejected | required | `pass` | rejected fixture `adeu_arc_scorecard_manifest_v93_reject_leaderboard_competition_overclaim_local_only.json` |
| Settlement posture carry remains explicit and fail-closed | required | `pass` | `settlement_posture_carry` validation and rejected fixture `adeu_arc_scorecard_manifest_v93_reject_settlement_posture_erasure.json` |
| Submission/tournament/operator authority leakage remains deferred | required | `pass` | rejected fixture `adeu_arc_scorecard_manifest_v93_reject_submission_tournament_operator_leakage.json` and lock hard constraints |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v93_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v93/evidence_inputs/metric_key_continuity_assertion_v93.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v93/evidence_inputs/runtime_observability_comparison_v93.json` |

## Stop-Gate Summary

```json
{
  "schema": "v93_closeout_stop_gate_summary@1",
  "arc": "vNext+93",
  "target_path": "V42-E",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v92": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": -18
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v92_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v93_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+92","baseline_elapsed_ms":108,"baseline_source":"artifacts/stop_gate/report_v92_closeout.md","current_arc":"vNext+93","current_elapsed_ms":90,"current_source":"artifacts/stop_gate/report_v93_closeout.md","delta_ms":-18,"notes":"v93 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-E scorecard baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42E Scorecard Evidence

```json
{"schema":"v42e_arc_scorecard_evidence@1","evidence_input_path":"artifacts/agent_harness/v93/evidence_inputs/v42e_arc_scorecard_evidence_v93.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS93.md#v93-continuation-contract-machine-checkable","merged_pr":"#315","merge_commit":"636e543039ff700e3795b2c367fd06bb509a5d20","scorecard_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_scorecard_manifest.v1.json","scorecard_mirror_schema_path":"spec/adeu_arc_scorecard_manifest.schema.json","accepted_reference_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus93/adeu_arc_scorecard_manifest_v93_reference.json"}
```

## Recommendation (Post v93)

- gate decision:
  - `V42E_SCORECARD_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v93 closes the bounded `V42-E` baseline with explicit source-kind discrimination,
    decomposed authority posture, competition-posture enums, local-vs-external replay
    separation, and fail-closed anti-overclaim posture on `main`.
  - direct online submission, tournament orchestration, and API/web operator widening
    remain deferred.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - the next default seam now belongs to post-`V42-E` widening selection rather than
    another `V42-E` continuation.
