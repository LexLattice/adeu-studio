# Draft Stop-Gate Decision (Pre-Start vNext+50)

This note reserves the pre-start threshold scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`

Status: draft decision scaffold (pre-start only, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "authoritative_scope": "v50_prestart_threshold_scaffold_only",
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This is a pre-start scaffold only. Planned evidence slots below are not closeout proof."
}
```

## Decision Guardrail (Frozen)

- This scaffold reserves v50 closeout slots only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`.
- This note is non-authoritative until v50 closes on `main`.
- `V34-A` downstream signing and closeout evidence remain authoritative prerequisites while
  v50 is still planning.
- Runtime-observability comparison evidence remains required and informational-only in this
  arc.

## Planned Evidence Source Shape

- expected CI workflow:
  - `ci` on `main`
- expected implementation PRs:
  - `Y1` declared matrix registry + parity report baseline
  - `Y2` matrix-lane guard suite + current-lane parity enforcement
- expected deterministic closeout artifacts:
  - `artifacts/quality_dashboard_v50_closeout.json`
  - `artifacts/stop_gate/metrics_v50_closeout.json`
  - `artifacts/stop_gate/report_v50_closeout.md`
- expected deterministic evidence input artifacts:
  - `artifacts/agent_harness/v50/evidence_inputs/runtime_observability_comparison_v50.json`
  - `artifacts/agent_harness/v50/evidence_inputs/metric_key_continuity_assertion_v50.json`
  - `artifacts/agent_harness/v50/evidence_inputs/v34b_matrix_parity_evidence_v50.json`
- expected deterministic matrix artifacts:
  - `artifacts/agent_harness/v50/matrix/adapter_matrix.json`
  - `artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json`

## Planned Exit-Criteria Check (vNext+50)

| Criterion | Threshold | Planned Result Slot | Evidence Slot |
|---|---|---|---|
| `Y1` merged with green CI | required | `pending` | merge commit + CI run |
| `Y2` merged with green CI | required | `pending` | merge commit + CI run |
| Stop-gate schema-family continuity retained | required | `pending` | `metrics_v50_closeout.json` |
| Stop-gate metric-key continuity retained | required | `pending` | `metric_key_continuity_assertion_v50.json` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | `metrics_v50_closeout.json` |
| Declared matrix registry emitted and schema-valid | required | `pending` | `adapter_matrix.json` |
| Matrix parity report emitted and schema-valid | required | `pending` | `adapter_matrix_parity_report.json` |
| Registry remains enabled-only and disabled rows are absent | required | `pending` | `adapter_matrix.json` |
| Frozen singleton runtime id enforced without host-inference drift | required | `pending` | `v34b_matrix_parity_evidence_v50.json` |
| Exact canonical subtree parity retained across current lanes | required | `pending` | `v34b_matrix_parity_evidence_v50.json` |
| Exact policy-equivalence parity retained across current lanes | required | `pending` | `v34b_matrix_parity_evidence_v50.json` |
| Matrix report hash and subject-key proof materialized | required | `pending` | `v34b_matrix_parity_evidence_v50.json` |
| Every declared lane appears exactly once in the matrix report | required | `pending` | `adapter_matrix_parity_report.json` + `v34b_matrix_parity_evidence_v50.json` |
| Undeclared, duplicate, or out-of-order lanes rejected fail closed | required | `pending` | merged guard suites |
| No boundary-release expansion introduced | required | `pending` | lock-scope audit |

Summary slot (to be completed only at closeout):

- `schema = "stop_gate_metrics@1"`
- `valid = null`
- `all_passed = null`
- `issues = []`
- `derived_cardinality = null`

## Planned Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v49_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v50_closeout.json",
  "expected_relation": "exact_keyset_equality",
  "expected_cardinality": 80,
  "metric_key_exact_set_equal_v49": null,
  "metric_key_cardinality": null
}
```

## Planned Runtime Observability Comparison (v49 Baseline vs v50 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_arc": "vNext+49",
  "current_arc": "vNext+50",
  "baseline_source": "artifacts/stop_gate/report_v49_closeout.md",
  "current_source": "artifacts/stop_gate/report_v50_closeout.md",
  "baseline_elapsed_ms": null,
  "current_elapsed_ms": null,
  "delta_ms": null,
  "notes": "Populate only at v50 closeout; runtime timing remains informational-only."
}
```

## Planned V34-B Matrix Parity Evidence

```json
{
  "schema": "v34b_matrix_parity_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md#v34b_matrix_baseline_contract@1",
  "matrix_registry_path": "artifacts/agent_harness/v50/matrix/adapter_matrix.json",
  "matrix_report_path": "artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json",
  "matrix_report_hash": null,
  "lane_id_tuple": [
    "deployment_mode",
    "adapter_id",
    "runtime_id"
  ],
  "enabled_row_policy": "registry_is_enabled_only_disabled_rows_forbidden_non_v50",
  "lane_count_authority": "all_registry_rows_only_because_disabled_rows_are_forbidden",
  "lane_count": null,
  "deployment_modes_covered": null,
  "adapter_ids_covered": null,
  "runtime_ids_covered": null,
  "singleton_runtime_id_enforced": null,
  "runtime_id_source_policy": "contract_derived_only_no_host_environment_inference",
  "runtime_id_host_inference_forbidden": null,
  "declared_registry_only": null,
  "lexicographic_lane_order_enforced": null,
  "canonical_subtree_exact_match_required": null,
  "canonical_subtree_source_policy": null,
  "policy_equivalence_exact_match_required": null,
  "policy_equivalence_subject_keys_verified": null,
  "policy_equivalence_value_shapes_verified": null,
  "report_covers_all_declared_lanes": null,
  "verification_passed": null,
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v49": null,
  "notes": "Populate only at v50 closeout after Y1/Y2 merge and closeout artifact generation."
}
```

## Pre-Start Failure Conditions (Scaffold)

- fail closed if baseline and current metrics artifact paths are identical.
- fail closed if planned v50 closeout attempts to claim a new stop-gate metric key without
  explicit lock release.
- fail closed if planned matrix parity evidence omits the declared registry/report artifacts.
- fail closed if planned matrix parity evidence omits `matrix_report_hash` or subject-key
  proof for the frozen parity subject.
- fail closed if planned matrix parity evidence omits canonical-subtree source proof,
  policy-equivalence value-shape proof, or report-completeness proof.
- fail closed if planned v50 closeout treats disabled rows as part of lane coverage, because
  the v50 registry is enabled-only.
- fail closed if planned v50 closeout accepts host- or container-inferred `runtime_id`
  values outside the frozen singleton.
- fail closed if planned v50 closeout claims multi-runtime coverage beyond the frozen
  singleton runtime-id posture.

## Recommendation (Pre-Start)

- gate decision:
  - `PENDING_VNEXT_PLUS50_EXECUTION`
- rationale:
  - v49 is closed and unblocks explicit `V34-B` evaluation,
  - current implementation supports an honest thin matrix baseline,
  - closeout proof must wait for actual Y1/Y2 implementation and evidence generation.
