# Draft Stop-Gate Decision (Post vNext+50)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`

Status: draft decision note (post-hoc closeout capture, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v50_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+50` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`.
- This note captures `V34-B` released-surface matrix-baseline closeout evidence only; it
  does not authorize `V34-C`..`V34-G` behavior release by itself.
- Declared matrix-lane registry authority, deterministic parity reporting, and canonical
  matrix-parity evidence remain artifact-authoritative, deterministic, and fail-closed under
  frozen lock text.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `48b54834be3c119b48372a59275a1c2c5f472aef`
- arc-completion CI run:
  - Run ID: `22763765454`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22763765454`
  - conclusion: `success`
- merged implementation PRs:
  - `#249` (`contracts: add v34b declared matrix registry and parity report baseline`)
  - `#250` (`tests: add v34b matrix-lane parity and registry guard suite`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v50_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v50_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v50_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v50/evidence_inputs/runtime_observability_comparison_v50.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v50/evidence_inputs/metric_key_continuity_assertion_v50.json`
  - matrix-parity evidence input:
    `artifacts/agent_harness/v50/evidence_inputs/v34b_matrix_parity_evidence_v50.json`
  - matrix registry artifact:
    `artifacts/agent_harness/v50/matrix/adapter_matrix.json`
  - matrix parity report artifact:
    `artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json`
- supporting deterministic matrix packaging artifacts (reproducible):
  - `artifacts/agent_harness/v50/matrix/adeu_integrated/`
  - `artifacts/agent_harness/v50/matrix/standalone/`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v50_closeout.json --baseline artifacts/quality_dashboard_v49_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v50_closeout.json --quality-baseline artifacts/quality_dashboard_v49_closeout.json --out-json artifacts/stop_gate/metrics_v50_closeout.json --out-md artifacts/stop_gate/report_v50_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python - <<'PY' ... generate v50 evidence_inputs/*.json plus v50 matrix/*.json from the v49/v50 stop-gate artifacts, a patched v46 closeout taskpack fixture, and current run/verify/write_closeout_evidence/package_ux/matrix_parity entrypoints ... PY`

## Exit-Criteria Check (vNext+50)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `Y1` merged with green CI | required | `pass` | PR `#249` merged; CI run `22762086927` is `success` |
| `Y2` merged with green CI | required | `pass` | PR `#250` merged; CI run `22763632418` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v49 and v50 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v49 and v50 keysets are exact-set equal (`added_keys = []`, `removed_keys = []`) |
| Deterministic cardinality continuity retained | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| Declared matrix registry emitted and schema-valid | required | `pass` | `artifacts/agent_harness/v50/matrix/adapter_matrix.json` |
| Matrix parity report emitted and schema-valid | required | `pass` | `artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json` |
| Registry remains enabled-only and disabled rows are absent | required | `pass` | `adapter_matrix.json` contains only declared enabled rows; `lane_count = 2` |
| Frozen singleton runtime id enforced without host-inference drift | required | `pass` | `runtime_ids_covered = ["local_python_cli"]` and `runtime_id_host_inference_forbidden = true` in `v34b_matrix_parity_evidence_v50.json` |
| Exact canonical subtree parity retained across current lanes | required | `pass` | `pairwise_parity[0].canonical_subtree_exact_match = true` in `adapter_matrix_parity_report.json` |
| Exact policy-equivalence parity retained across current lanes | required | `pass` | `pairwise_parity[0].policy_equivalence_exact_match = true` in `adapter_matrix_parity_report.json` |
| Matrix report hash and subject-key proof materialized | required | `pass` | `artifacts/agent_harness/v50/evidence_inputs/v34b_matrix_parity_evidence_v50.json` |
| Every declared lane appears exactly once in the matrix report | required | `pass` | `lane_count = 2` and `report_covers_all_declared_lanes = true` across matrix report and matrix evidence |
| Undeclared, duplicate, or out-of-order lanes rejected fail closed | required | `pass` | merged Y2 guard suites in `packages/adeu_agent_harness/tests/test_taskpack_packaging.py` and `packages/adeu_agent_harness/tests/test_taskpack_verifier.py` |
| No boundary-release expansion introduced | required | `pass` | v50 scope remains `V34-B` released-surface baseline only |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `derived_cardinality = 80` (computed from `metrics` keyset cardinality)

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v49_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v50_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v49 Baseline vs v50 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+49",
  "current_arc": "vNext+50",
  "baseline_source": "artifacts/stop_gate/report_v49_closeout.md",
  "current_source": "artifacts/stop_gate/report_v50_closeout.md",
  "baseline_elapsed_ms": 97,
  "current_elapsed_ms": 100,
  "delta_ms": 3,
  "notes": "v50 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+49` baseline | `artifacts/stop_gate/metrics_v49_closeout.json` | `22` | `78` | `97` | `68230` | `204690` | `true` | `true` |
| `vNext+50` closeout | `artifacts/stop_gate/metrics_v50_closeout.json` | `22` | `78` | `100` | `68230` | `204690` | `true` | `true` |

## V34-B Matrix Parity Evidence

```json
{
  "schema": "v34b_matrix_parity_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md#v34b_matrix_baseline_contract@1",
  "matrix_registry_path": "artifacts/agent_harness/v50/matrix/adapter_matrix.json",
  "matrix_report_path": "artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json",
  "matrix_report_hash": "62f13430f7225daf3f5731fc8a30d928a71c68f2102214c411c258d9f8221fa1",
  "lane_id_tuple": [
    "deployment_mode",
    "adapter_id",
    "runtime_id"
  ],
  "enabled_row_policy": "registry_is_enabled_only_disabled_rows_forbidden_non_v50",
  "lane_count_authority": "all_registry_rows_only_because_disabled_rows_are_forbidden",
  "lane_count": 2,
  "deployment_modes_covered": [
    "adeu_integrated",
    "standalone"
  ],
  "adapter_ids_covered": [
    "v45_default"
  ],
  "runtime_ids_covered": [
    "local_python_cli"
  ],
  "singleton_runtime_id_enforced": true,
  "runtime_id_source_policy": "contract_derived_only_no_host_environment_inference",
  "runtime_id_host_inference_forbidden": true,
  "declared_registry_only": true,
  "lexicographic_lane_order_enforced": true,
  "canonical_subtree_exact_match_required": true,
  "canonical_subtree_source_policy": "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only",
  "policy_equivalence_exact_match_required": true,
  "policy_equivalence_subject_keys_verified": [
    "allowlist_violations",
    "forbidden_effects_detected",
    "issue_code_set",
    "required_evidence_slots_filled"
  ],
  "policy_equivalence_value_shapes_verified": {
    "issue_code_set": "lexicographically_sorted_unique_string_list_canonical_form",
    "required_evidence_slots_filled": "boolean",
    "allowlist_violations": "lexicographically_sorted_unique_normalized_posix_path_list",
    "forbidden_effects_detected": "boolean"
  },
  "report_covers_all_declared_lanes": true,
  "verification_passed": true,
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v49": true,
  "notes": "v50 Y1/Y2 merged with declared matrix registry, deterministic parity reporting, registry-backed guard suites, and canonical matrix-parity evidence on main."
}
```

## Recommendation (Post v50)

- gate decision:
  - `GO_VNEXT_PLUS51_PLANNING_DRAFT`
- rationale:
  - v50 closes the released-surface `V34-B` baseline with a declared matrix registry,
    deterministic parity report, and canonical matrix-parity evidence on `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout
    evidence.
  - future planning no longer needs to treat declared current-lane matrix parity as a
    missing baseline.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`,
   `docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md`, and
   `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md` from a fresh post-v50 planning pass.
2. Keep v50 closeout artifacts stable; rerun closeout commands only under the frozen
   deterministic env contract.
3. Carry only explicit follow-on paths into future planning:
   broader matrix expansion beyond current released adapter/mode sets,
   `V34-C` zero-trust recomputation,
   `V34-D` retry-context automation,
   and remote/enclave follow-on lanes under explicit future lock text.
