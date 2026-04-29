# Draft Stop-Gate Decision (Post vNext+204)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS204.md`

Status: draft decision note (post-closeout capture, April 29, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS204.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v204_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+204` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS204.md`.
- This note captures bounded `V73-B` closeout evidence only on `main`; it does
  not authorize `V73-C` self-improvement ledger rows, promotion / demotion
  recommendations, `V74` operator/product projection, `V75` dispatch, runtime
  permission, release authority, or external contest participation.
- Canonical `V73-B` shipment in `v204` is carried by bounded
  `adeu_repo_description` candidate outcome observation, regression, and
  tool-fitness drift models, validators, schema exports, deterministic
  `vnext_plus204` reference and reject fixtures, and canonical
  `v73b_candidate_outcome_observation_evidence@1` evidence input under
  `artifacts/agent_harness/v204/evidence_inputs/`.

## Evidence Source

- merged implementation PR:
  - `#432` (`Implement V73-B outcome observation surfaces`)
- arc-completion merge commit:
  - `f6578619abf1460f1061a69b9695b5ad4eb6500e`
- merged-at timestamp:
  - `2026-04-27T16:44:52Z`
- implementation commits integrated by the merge:
  - `b16f873124781e9d8c6f521985d6ac77adf60724`
    (`Implement V73-B outcome observation surfaces`)
- implementation verification recorded before PR / update:
  - focused pytest
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=204`
- deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v204_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v204_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v204_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v204/evidence_inputs/metric_key_continuity_assertion_v204.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v204/evidence_inputs/runtime_observability_comparison_v204.json`
  - `V73-B` candidate outcome observation evidence input:
    `artifacts/agent_harness/v204/evidence_inputs/v73b_candidate_outcome_observation_evidence_v204.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v204/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS204_EDGES.md`

## Exit-Criteria Check (vNext+204)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V73-B` merged on `main` | required | `pass` | PR `#432`, merge commit `f6578619abf1460f1061a69b9695b5ad4eb6500e` |
| Implementation stayed in the repo-description lane | required | `pass` | merged implementation package is `adeu_repo_description` |
| Selected observation / regression / tool-fitness surfaces shipped | required | `pass` | `repo_candidate_outcome_observation_record@1`, `repo_outcome_regression_register@1`, and `repo_tool_fitness_drift_register@1` |
| Released `V73-A` substrate is consumed | required | `pass` | V73-B rows reference released `vnext_plus203` entry, source-index, horizon, and guardrail fixtures |
| Benefit observation has an evidence floor | required | `pass` | benefit rows require outcome source refs, baseline refs, intervention refs, evaluation refs, and non-promotion guardrail refs |
| Blocking regressions cannot be hidden | required | `pass` | review hardening added reciprocal regression linkage and carry-forward enforcement |
| No-regression posture is checked | required | `pass` | no-regression rows require checked evaluation horizon coverage or negative-control refs |
| Tool-fitness drift remains target-bound | required | `pass` | confirmed/misleading tool-fit rows require target horizons, target namespace, prior applicability, and observed result refs |
| Global tool-policy claims are rejected | required | `pass` | global tool-fitness reject fixture passed |
| Observation remains non-promotional | required | `pass` | observation-as-promotion reject fixture passed |
| Regression remains non-implementation | required | `pass` | regression-as-implementation-priority reject fixture passed |
| `V73-C` stayed deferred | required | `pass` | no ledger, operator-cognition signal, recommendation, or family closeout alignment surfaces shipped |
| Release, product, runtime, dispatch, and external contest authority remain forbidden | required | `pass` | no downstream authority surfaces selected |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v204_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v204/evidence_inputs/metric_key_continuity_assertion_v204.json` records exact keyset equality versus `v203` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v204/evidence_inputs/runtime_observability_comparison_v204.json` records `91 ms` baseline, `120 ms` current, `29 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v204_closeout_stop_gate_summary@1",
  "arc": "vNext+204",
  "target_path": "V73-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v203": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 120,
  "runtime_observability_delta_ms": 29
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v203_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v204_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+203","baseline_elapsed_ms":91,"baseline_source":"artifacts/stop_gate/report_v203_closeout.md","current_arc":"vNext+204","current_elapsed_ms":120,"current_source":"artifacts/stop_gate/report_v204_closeout.md","delta_ms":29,"notes":"v204 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while closing the bounded V73-B outcome observation, regression, and tool-fitness drift starter slice on main: repo-owned adeu_repo_description package only, three repo_* V73-B surfaces, source-bound consumption of released V73-A entry/source-index/guardrail substrate, benefit observations require outcome sources plus baseline/intervention/evaluation/guardrail refs, reciprocal regression linkage prevents hidden blocking regressions, target-bound tool-fitness drift remains non-global, and no self-improvement ledger, promotion, demotion, adoption, release, product authorization, runtime permission, dispatch, or external contest participation.","schema":"runtime_observability_comparison@1"}
```

## V73B Candidate Outcome Observation Evidence

```json
{"benefit_observation_requires_horizon_and_guardrail_refs":true,"benefit_observation_requires_outcome_source_refs":true,"blocking_regressions_must_be_carried_forward":true,"ci_checks":["python","web","lean-formal"],"consumed_record_shapes":["repo_candidate_outcome_review_entry@1","repo_outcome_evidence_source_index@1","repo_outcome_review_boundary_guardrail@1"],"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS204.md#machine-checkable-contract","evidence_input_path":"artifacts/agent_harness/v204/evidence_inputs/v73b_candidate_outcome_observation_evidence_v204.json","global_tool_fitness_claims_rejected":true,"implementation_commits":["b16f873124781e9d8c6f521985d6ac77adf60724"],"implementation_packages":["adeu_repo_description"],"implementation_source_path":"packages/adeu_repo_description/src/adeu_repo_description/candidate_outcome_review.py","local_full_python_gate":"make check","merge_commit":"f6578619abf1460f1061a69b9695b5ad4eb6500e","merged_at":"2026-04-27T16:44:52Z","merged_pr":"#432","metric_key_continuity_assertion_path":"artifacts/agent_harness/v204/evidence_inputs/metric_key_continuity_assertion_v204.json","no_regression_requires_checked_horizon_or_negative_control":true,"notes":"v204 evidence pins the bounded V73-B closeout seam on main: outcome observation rows consume released V73-A entries/sources/horizons/guardrails; benefit observations require explicit outcome sources, baseline/intervention/evaluation horizons, and non-promotion guardrails; regression rows are reciprocally linked to observations and blocking regressions must be carried forward; tool-fitness drift is target-bound to declared horizons/namespace/prior applicability; and no row authorizes self-approval, promotion, demotion, adoption, release, product, runtime, dispatch, or external contest participation.","observation_as_promotion_rejected":true,"observation_record_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_candidate_outcome_observation_record.v1.json","observation_record_mirror_schema_path":"spec/repo_candidate_outcome_observation_record.schema.json","observation_record_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus204/repo_candidate_outcome_observation_record_v204_reference.json","package_export_surface_path":"packages/adeu_repo_description/src/adeu_repo_description/__init__.py","regression_as_implementation_priority_rejected":true,"regression_register_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_outcome_regression_register.v1.json","regression_register_mirror_schema_path":"spec/repo_outcome_regression_register.schema.json","regression_register_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus204/repo_outcome_regression_register_v204_reference.json","regression_reverse_linkage_enforced":true,"reject_fixture_dir":"apps/api/fixtures/repo_description/vnext_plus204","runtime_event_stream_path":"artifacts/agent_harness/v204/runtime/evidence/local/urm_events.ndjson","runtime_observability_comparison_path":"artifacts/agent_harness/v204/evidence_inputs/runtime_observability_comparison_v204.json","schema":"v73b_candidate_outcome_observation_evidence@1","schema_export_source_path":"packages/adeu_repo_description/src/adeu_repo_description/export_schema.py","selected_external_contest_participation_for_v73b":false,"selected_product_authorization_for_v73b":false,"selected_record_shapes":["repo_candidate_outcome_observation_record@1","repo_outcome_regression_register@1","repo_tool_fitness_drift_register@1"],"selected_runtime_permission_or_dispatch_for_v73b":false,"selected_v73c_ledger_or_recommendation_for_v73b":false,"test_reference_path":"packages/adeu_repo_description/tests/test_candidate_outcome_review_v73b.py","tool_fitness_drift_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_tool_fitness_drift_register.v1.json","tool_fitness_drift_mirror_schema_path":"spec/repo_tool_fitness_drift_register.schema.json","tool_fitness_drift_reference_fixture_path":"apps/api/fixtures/repo_description/vnext_plus204/repo_tool_fitness_drift_register_v204_reference.json","tool_fitness_target_bound":true}
```

## Recommendation (Post v204)

- gate decision:
  - `V73B_OUTCOME_OBSERVATION_REGRESSION_TOOL_FITNESS_COMPLETE_ON_MAIN`
- rationale:
  - `v204` closes the bounded `V73-B` outcome observation starter seam on
    `main`;
  - the shipped slice stayed properly bounded:
    - same repo-owned implementation package (`adeu_repo_description`) only
    - three `repo_*` V73-B record surfaces
    - source-bound consumption of released `V73-A` entry, source-index,
      horizon, and guardrail substrate
    - explicit benefit evidence floor, including outcome source refs
    - reciprocal regression linkage and blocking-regression carry-forward
      enforcement
    - checked no-regression posture over horizon or negative-control evidence
    - target-bound tool-fitness drift, not global tool policy
    - no self-improvement ledger, operator-cognition outcome signal,
      promotion / demotion recommendation, adoption, release, product
      authorization, runtime permission, external contest participation, or
      dispatch widening
  - stop-gate schema-family and metric-key continuity stayed intact.
  - runtime observability remained informational-only.
  - `V73-B` is now closed on `main`.
  - `V73` remains open for the reviewed `V73-C` lifecycle slice.
  - the next selected starter is `V73-C`: self-improvement outcome ledger,
    operator-cognition outcome signal, promotion / demotion recommendation, and
    family closeout alignment.
