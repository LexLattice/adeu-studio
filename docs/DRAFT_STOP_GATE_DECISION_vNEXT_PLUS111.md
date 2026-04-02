# Draft Stop-Gate Decision (Post vNext+111)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS111.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS111.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v111_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+111` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS111.md`.
- This note captures bounded `V47-F` benchmark-world consumer evidence only; it does
  not authorize `V46` benchmark-family release, official scorecard or leaderboard
  authority, repo-wide markdown migration, execution posture, approval posture,
  waiver issuance, deferral issuance, or current markdown supersession by itself.
- Canonical `V47-F` release in v111 is carried by the shipped
  `adeu_semantic_source` / `adeu_commitments_ir` source, model, schema-export, and
  deterministic fixture surfaces plus the canonical
  `v47f_authoritative_normative_markdown_benchmark_policy_consumer_evidence@1`
  evidence input under `artifacts/agent_harness/v111/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#333` (`V47-F: add ANM benchmark consumer binding profile`)
- arc-completion merge commit: `787aa1e864ea936bfe3c94199092cdc60560d916`
- merged-at timestamp: `2026-04-02T12:47:08Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v111_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v111_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v111_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v111/evidence_inputs/metric_key_continuity_assertion_v111.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v111/evidence_inputs/runtime_observability_comparison_v111.json`
  - `V47-F` release evidence input:
    `artifacts/agent_harness/v111/evidence_inputs/v47f_authoritative_normative_markdown_benchmark_policy_consumer_evidence_v111.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v111/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS111_EDGES.md`

## Exit-Criteria Check (vNext+111)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V47-F` merged with green CI | required | `pass` | PR `#333`, merge commit `787aa1e864ea936bfe3c94199092cdc60560d916`, checks `python/web/lean-formal = pass` |
| Released benchmark consumer binding profile ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_commitments_ir/schema/anm_benchmark_policy_consumer_binding_profile.v1.json`, `spec/anm_benchmark_policy_consumer_binding_profile.schema.json`, and parity coverage in `packages/adeu_commitments_ir/tests/test_export_schema.py` |
| Benchmark-world and benchmark-ref vocabularies stay exact and bounded | required | `pass` | `BenchmarkConsumerWorldKind` / `BenchmarkConsumerRefKind` typing in `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`, committed profile fixture, and tests `test_v47f_vocabularies_are_exact` plus `test_v47f_accepts_all_three_benchmark_worlds` |
| Every accepted benchmark row binds exactly one explicit released `D-IR` clause source | required | `pass` | `AnmBenchmarkPolicyConsumerRow` in `anm_models.py`, compile-time clause resolution in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, accepted spec `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`, and deterministic replay in `test_v47f_reference_profile_replays_deterministically` |
| Result-set and ledger refs remain support-only and fail closed on contradiction or wrong-target attachment | required | `pass` | support-surface validation in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, reject spec `packages/adeu_semantic_source/tests/fixtures/v47f/reject_support_only_authority_spec.json`, and tests `test_v47f_rejects_support_only_authority_claim`, `test_v47f_rejects_contradictory_supporting_surfaces`, and `test_v47f_rejects_supporting_surface_with_wrong_target` |
| Benchmark refs resolve fail closed against snapshot/source-scope bindings and repo-root/readable-file constraints | required | `pass` | benchmark-registry resolution in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, reject spec `packages/adeu_semantic_source/tests/fixtures/v47f/reject_unresolved_local_eval_ref_spec.json`, and tests `test_v47f_rejects_unresolved_local_eval_ref`, `test_v47f_rejects_benchmark_ref_outside_repo_root`, and `test_v47f_wraps_unreadable_benchmark_ref_as_compile_error` |
| Benchmark rows respect released `V42-D`, `V42-E`, and `V42-G4` doctrine | required | `pass` | released benchmark-world vocabularies in `anm_models.py`, accepted benchmark rows in `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`, and test `test_v47f_accepts_all_three_benchmark_worlds` |
| Benchmark rows respect released `V47-C`, `V47-D`, and `V47-E` doctrine | required | `pass` | required coexistence / ownership / downstream consumer profile inputs in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, reject spec `packages/adeu_semantic_source/tests/fixtures/v47f/reject_bypass_upstream_profile_spec.json`, and test `test_v47f_rejects_bypass_upstream_profile` |
| Action vocabulary remains exact, shared, pairwise disjoint, and consistent with authority relation | required | `pass` | `AllowedBenchmarkConsumerAction` typing and action-list validation in `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`, committed profile fixture, and tests `test_v47f_vocabularies_are_exact` and `test_v47f_rejects_overlapping_action_lists` |
| Accepted benchmark fixtures stay deterministic across local-eval, scorecard, and behavior-evidence worlds | required | `pass` | `packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json`, `packages/adeu_commitments_ir/tests/fixtures/v47f/reference_anm_benchmark_policy_consumer_binding_profile.json`, and `test_v47f_reference_profile_replays_deterministically` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v111_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v111/evidence_inputs/metric_key_continuity_assertion_v111.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v111/evidence_inputs/runtime_observability_comparison_v111.json` |

## Stop-Gate Summary

```json
{
  "schema": "v111_closeout_stop_gate_summary@1",
  "arc": "vNext+111",
  "target_path": "V47-F",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v110": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 111,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v110_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v111_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+110","current_arc":"vNext+111","baseline_source":"artifacts/stop_gate/report_v110_closeout.md","current_source":"artifacts/stop_gate/report_v111_closeout.md","baseline_elapsed_ms":111,"current_elapsed_ms":111,"delta_ms":0,"notes":"v111 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V47-F benchmark-world consumer lane: one canonical anm_benchmark_policy_consumer_binding_profile@1, exact benchmark-world and benchmark-ref vocabularies, exactly one released D-IR clause source per benchmark row, support-only result/ledger posture with fail-closed contradiction and target-lineage coherence, explicit respect for released V42-D local-eval posture, V42-E scorecard authority posture, V42-G4 behavior-evidence boundary posture, and retained constrain-only non-executive authority boundaries."}
```

## V47F Authoritative Normative Markdown Benchmark Policy Consumer Evidence

```json
{"schema":"v47f_authoritative_normative_markdown_benchmark_policy_consumer_evidence@1","evidence_input_path":"artifacts/agent_harness/v111/evidence_inputs/v47f_authoritative_normative_markdown_benchmark_policy_consumer_evidence_v111.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS111.md#v111-continuation-contract-machine-checkable","merged_pr":"#333","merge_commit":"787aa1e864ea936bfe3c94199092cdc60560d916","implementation_packages":["adeu_semantic_source","adeu_commitments_ir"],"benchmark_consumer_profile_implementation_source_path":"packages/adeu_semantic_source/src/adeu_semantic_source/anm.py","benchmark_consumer_profile_model_source_path":"packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py","benchmark_consumer_profile_authoritative_schema_path":"packages/adeu_commitments_ir/schema/anm_benchmark_policy_consumer_binding_profile.v1.json","benchmark_consumer_profile_mirror_schema_path":"spec/anm_benchmark_policy_consumer_binding_profile.schema.json","test_reference_paths":["packages/adeu_semantic_source/tests/test_anm_benchmark_policy_consumer.py","packages/adeu_commitments_ir/tests/test_anm_benchmark_policy_consumer_binding_profile.py","packages/adeu_commitments_ir/tests/test_export_schema.py"],"accepted_benchmark_consumer_spec_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47f/reference_benchmark_policy_consumer_spec.json","accepted_profile_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47f/reference_anm_benchmark_policy_consumer_binding_profile.json","rejected_support_only_authority_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47f/reject_support_only_authority_spec.json","rejected_world_ref_kind_mismatch_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47f/reject_world_ref_kind_mismatch_spec.json","rejected_unresolved_local_eval_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47f/reject_unresolved_local_eval_ref_spec.json","rejected_bypass_upstream_profile_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47f/reject_bypass_upstream_profile_spec.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v111/evidence_inputs/metric_key_continuity_assertion_v111.json","runtime_observability_comparison_path":"artifacts/agent_harness/v111/evidence_inputs/runtime_observability_comparison_v111.json","runtime_event_stream_path":"artifacts/agent_harness/v111/runtime/evidence/local/urm_events.ndjson","notes":"v111 evidence pins the released V47-F benchmark-world consumer baseline on main: one canonical anm_benchmark_policy_consumer_binding_profile@1, explicit local-eval, scorecard, and behavior-evidence benchmark rows, exact world/ref-kind invariants, exactly one authoritative D-IR clause source per row, support-only result/ledger references with fail-closed contradiction and target-lineage coherence, explicit respect for released V42-D, V42-E, and V42-G4 doctrine, explicit respect for released V47-C coexistence doctrine, V47-D ownership-transition doctrine, and V47-E consumer doctrine, plus retained constrain-only non-executive authority posture."}
```

## Recommendation (Post v111)

- gate decision:
  - `V47F_AUTHORITATIVE_NORMATIVE_MARKDOWN_BENCHMARK_POLICY_CONSUMER_COMPLETE_ON_MAIN`
  - `V47_AUTHORITATIVE_NORMATIVE_MARKDOWN_BRANCH_COMPLETE_ON_MAIN`
- rationale:
  - v111 closes the bounded `V47-F` benchmark-world consumer seam on `main` by
    taking the released `V47-A` + `V47-B` + `V47-C` + `V47-D` + `V47-E` ANM stack
    and making benchmark-world consumer posture explicit in one typed profile.
  - the shipped slice is doctrine-first and non-executive: it does not reopen ANM
    source syntax, normalized `D-IR`, checker facts, result-set grammar, ledger
    semantics, coexistence/adoption doctrine, ownership-transition doctrine,
    descriptive/runtime consumer doctrine, `V46` benchmark-family release, or
    repo-wide markdown migration.
  - benchmark rows now carry exact world/ref-kind invariants and exactly one bound
    released `D-IR` clause source, so policy authority is no longer implied by raw
    benchmark artifact presence or support-surface attachment.
  - result-set refs and ledger refs remain support-only and fail closed when they
    contradict the bound policy source, contradict each other, or attach to the wrong
    benchmark target lineage.
  - benchmark binding must respect released `V42-D` local-eval posture, released
    `V42-E` scorecard posture, released `V42-G4` behavior-evidence posture, plus the
    released `V47-C`, `V47-D`, and `V47-E` upstream ANM profiles where those
    profiles are relevant to the benchmark ref.
  - local-eval, scorecard, and behavior-evidence benchmark consumers are now explicit
    and bounded, while official benchmark-family release, submission/tournament
    authority, and execution-facing seams remain outside this closed family.
  - authoritative schema, mirrored export, committed fixtures, and targeted tests stay
    in parity for the released benchmark consumer surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v110 baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v30.md` now records the bounded `V47-A` through
    `V47-F` ladder as complete on `main`, with no further internal `V47` path
    currently selected.
