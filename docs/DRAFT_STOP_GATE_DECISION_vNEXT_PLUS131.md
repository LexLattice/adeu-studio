# Draft Stop-Gate Decision (Post vNext+131)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS131.md`

Status: draft decision note (post-hoc closeout capture, April 5, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS131.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v131_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+131` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS131.md`.
- This note captures bounded `V44-A` reasoning-assessment substrate evidence only; it
  does not authorize taxonomy release, model-profile aggregation, benchmark scoring,
  SRM architecture, or contest/runtime-selection doctrine by itself.
- Canonical `V44-A` release in `v131` is carried by the shipped
  `packages/adeu_reasoning_assessment` package, authoritative and mirrored schema
  exports, deterministic `v44a` fixtures/tests, and the canonical
  `v44a_reasoning_assessment_contract_evidence@1` evidence input under
  `artifacts/agent_harness/v131/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` now marks `V44-A`
  closed on `main` and advances the branch-local default next path to `V44-B`; it
  does not complete the whole `V44` family by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#353` (`feat(v131): add reasoning assessment contracts`)
- arc-completion merge commit: `247205ada7c7e6244cc550cff3199cfd4fca4702`
- merged-at timestamp: `2026-04-05T02:38:08Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v131_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v131_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v131_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v131/evidence_inputs/metric_key_continuity_assertion_v131.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v131/evidence_inputs/runtime_observability_comparison_v131.json`
  - `V44-A` release evidence input:
    `artifacts/agent_harness/v131/evidence_inputs/v44a_reasoning_assessment_contract_evidence_v131.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS131_EDGES.md`

## Exit-Criteria Check (vNext+131)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V44-A` merged with green CI | required | `pass` | PR `#353`, merge commit `247205ada7c7e6244cc550cff3199cfd4fca4702`, checks `python/web/lean-formal = pass` |
| `packages/adeu_reasoning_assessment` is the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_reasoning_assessment` plus `Makefile` bootstrap wiring |
| Authoritative and mirror schemas ship deterministically | required | `pass` | `packages/adeu_reasoning_assessment/schema/*.json`, `spec/adeu_reasoning_template_probe.schema.json`, `spec/adeu_structural_reasoning_trace.schema.json`, and schema export replay coverage |
| Flat and hierarchical reference probes validate cleanly | required | `pass` | `reference_reasoning_template_probe_flat.json`, `reference_reasoning_template_probe_hierarchical.json`, and `test_reference_probes_and_traces_validate` |
| Clean and lawful-blocked reference traces validate cleanly | required | `pass` | `reference_structural_reasoning_trace_clean.json`, `reference_structural_reasoning_trace_blocked.json`, and `validate_trace_against_probe(...)` coverage |
| Reject fixtures fail closed for invalid early closure and invalid return-to-parent evidence | required | `pass` | committed reject fixtures plus model-validation and probe/trace validation tests |
| Completed traces must cover the full top-level plan spine | required | `pass` | review-hardening commit `593dc95` plus `test_completed_trace_missing_trailing_plan_step_fails_closed` |
| Blocked posture remains distinct from invalid early closure | required | `pass` | released terminal status vocabulary and reject-fixture coverage |
| No taxonomy, profile, or benchmark-scoring fields ship in `V44-A` | required | `pass` | package exports and schema surfaces contain probe/trace contracts only |
| Root `spec/` mirrors are claimed in docs and actually shipped | required | `pass` | merged `spec/adeu_reasoning_template_probe.schema.json` and `spec/adeu_structural_reasoning_trace.schema.json` |
| Local full Python gate passed | required | `pass` | `make check` passed locally before PR update and again after review hardening |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v131_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v131/evidence_inputs/metric_key_continuity_assertion_v131.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v131/evidence_inputs/runtime_observability_comparison_v131.json` |

## Stop-Gate Summary

```json
{
  "schema": "v131_closeout_stop_gate_summary@1",
  "arc": "vNext+131",
  "target_path": "V44-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v130": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 86,
  "runtime_observability_delta_ms": -21
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v130_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v131_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+130","current_arc":"vNext+131","baseline_source":"artifacts/stop_gate/report_v130_closeout.md","current_source":"artifacts/stop_gate/report_v131_closeout.md","baseline_elapsed_ms":107,"current_elapsed_ms":86,"delta_ms":-21,"notes":"v131 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V44-A reasoning-assessment starter substrate: one repo-owned adeu_reasoning_assessment package only, authoritative and mirrored schema export for adeu_reasoning_template_probe@1 and adeu_structural_reasoning_trace@1, explicit flat and single-level hierarchical probe posture, explicit blocked versus invalid early closure separation, explicit structural-break evidence posture, deterministic v44a fixtures, and review hardening for Windows-path schema export guards plus completed-trace full-plan-spine enforcement."}
```

## V44A Reasoning Assessment Contract Evidence

```json
{"schema":"v44a_reasoning_assessment_contract_evidence@1","evidence_input_path":"artifacts/agent_harness/v131/evidence_inputs/v44a_reasoning_assessment_contract_evidence_v131.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS131.md#v131-continuation-contract-machine-checkable","merged_pr":"#353","merge_commit":"247205ada7c7e6244cc550cff3199cfd4fca4702","implementation_packages":["adeu_reasoning_assessment"],"reasoning_assessment_package_root":"packages/adeu_reasoning_assessment","reasoning_assessment_pyproject_path":"packages/adeu_reasoning_assessment/pyproject.toml","reasoning_assessment_models_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/models.py","reasoning_assessment_export_schema_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/export_schema.py","reasoning_assessment_package_init_source_path":"packages/adeu_reasoning_assessment/src/adeu_reasoning_assessment/__init__.py","reasoning_template_probe_authoritative_schema_path":"packages/adeu_reasoning_assessment/schema/adeu_reasoning_template_probe.v1.json","reasoning_template_probe_mirror_schema_path":"spec/adeu_reasoning_template_probe.schema.json","structural_reasoning_trace_authoritative_schema_path":"packages/adeu_reasoning_assessment/schema/adeu_structural_reasoning_trace.v1.json","structural_reasoning_trace_mirror_schema_path":"spec/adeu_structural_reasoning_trace.schema.json","accepted_flat_probe_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reference_reasoning_template_probe_flat.json","accepted_hierarchical_probe_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reference_reasoning_template_probe_hierarchical.json","accepted_clean_trace_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reference_structural_reasoning_trace_clean.json","accepted_blocked_trace_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reference_structural_reasoning_trace_blocked.json","fixture_expectation_matrix_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reference_v44a_fixture_expectation_matrix.json","reject_invalid_early_closure_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reject_structural_reasoning_trace_invalid_early_closure_posture.json","reject_invalid_return_fixture_path":"packages/adeu_reasoning_assessment/tests/fixtures/v44a/reject_structural_reasoning_trace_invalid_return_to_parent.json","test_reference_path":"packages/adeu_reasoning_assessment/tests/test_reasoning_assessment_models.py","lane_vocabulary":["O","E","D","U"],"template_class_vocabulary":["lane_preserving_decomposition","branching_under_uncertainty","local_repair_continuation"],"trace_event_vocabulary":["step_activate","step_complete","branch_select","blocked","invalid_early_closure","repair_enter","repair_exit","return_to_parent"],"terminal_trace_status_vocabulary":["completed_clean","completed_with_structural_break","blocked","invalid_early_closure"],"hierarchical_depth_posture":"single_level_parent_child_only","blocked_invalid_closure_distinction_preserved":true,"structural_break_evidence_required":true,"taxonomy_profile_benchmark_fields_forbidden":true,"review_hardening_commit":"593dc95","metric_key_continuity_assertion_path":"artifacts/agent_harness/v131/evidence_inputs/metric_key_continuity_assertion_v131.json","runtime_observability_comparison_path":"artifacts/agent_harness/v131/evidence_inputs/runtime_observability_comparison_v131.json","runtime_event_stream_path":"artifacts/agent_harness/v131/runtime/evidence/local/urm_events.ndjson","notes":"v131 evidence pins the released V44-A reasoning-assessment starter substrate on main: one repo-owned adeu_reasoning_assessment package only, authoritative and mirrored schema export for adeu_reasoning_template_probe@1 and adeu_structural_reasoning_trace@1, explicit flat and single-level hierarchical probe posture, explicit plan-spine and return-to-parent trace law, explicit blocked versus invalid early closure separation, explicit structural-break evidence posture, deterministic v44a fixtures and fixture-expectation matrix, no taxonomy or profile aggregation, no benchmark scoring or promotion, and review hardening that fixed Windows-path schema export guards and fail-closed completed-trace full-plan-spine validation."}
```

## Recommendation (Post v131)

- gate decision:
  - `V44A_REASONING_ASSESSMENT_STARTER_COMPLETE_ON_MAIN`
  - `V44_REASONING_ASSESSMENT_FAMILY_CONTINUES_WITH_V44B_NEXT`
- rationale:
  - `v131` closes the bounded `V44-A` starter seam on `main` by shipping the
    contract-first assessment object before any taxonomy, profile, or benchmark lane
    can claim downstream authority.
  - the released slice stays narrow and evidence-first: one package, one probe
    contract, one trace contract, deterministic fixtures, authoritative/mirror schema
    exports, and no scoring or promotion surfaces.
  - hierarchical reasoning law is now real contract surface rather than prose only:
    explicit plan-spine refs, active-step posture, child ordering, return-to-parent
    evidence, and explicit structural-break records.
  - review hardening improved the actual contract safety without widening scope:
    Windows absolute-path detection in schema export is now correct, and completed
    traces must activate the full top-level plan spine.
  - the imported benchmarking bundle remains support-only and non-precedent; live
    ownership is fully re-authored in repo-native `packages/adeu_reasoning_assessment`.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability improved informationally (`-21 ms` vs `v130` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v27.md` should now be read with `V44-A` closed on
    `main` and `V44-B` as the branch-local default next path.
