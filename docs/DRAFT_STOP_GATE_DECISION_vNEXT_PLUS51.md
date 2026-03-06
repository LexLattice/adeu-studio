# Draft Stop-Gate Decision (Post vNext+51)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`

Status: draft decision note (post-hoc closeout capture, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS51.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v51_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+51` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md`.
- This note captures `V34-C` verifier-lane policy-recompute closeout evidence only; it does
  not authorize `V34-D`..`V34-G` behavior release by itself.
- Shared canonical recompute authority, deterministic `policy_recompute_result@1` emission,
  verifier mismatch fail-closed behavior, and cumulative closeout evidence integration remain
  artifact-authoritative, deterministic, and fail-closed under frozen lock text.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `4786aa4847c749e9a26de54d3ddbe254ec67e279`
- arc-completion CI run:
  - Run ID: `22773514719`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22773514719`
  - conclusion: `success`
- merged implementation PRs:
  - `#251` (`contracts: add v34c policy recompute result baseline`)
  - `#252` (`tests: add v34c verifier mismatch and evidence guards`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v51_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v51_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v51_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v51/evidence_inputs/runtime_observability_comparison_v51.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v51/evidence_inputs/metric_key_continuity_assertion_v51.json`
  - policy-recompute evidence input:
    `artifacts/agent_harness/v51/evidence_inputs/v34c_policy_recompute_evidence_v51.json`
  - policy recompute artifact:
    `artifacts/agent_harness/v51/recompute/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.json`
- supporting deterministic verifier/evidence artifacts (reproducible):
  - closeout profile:
    `artifacts/agent_harness/v51/profiles/v51_closeout_profile.json`
  - taskpack profile registry:
    `artifacts/agent_harness/v51/taskpack_profile_registry.json`
  - compiled closeout taskpack:
    `artifacts/agent_harness/v51/taskpacks/v41/v51_closeout/`
  - closeout candidate change plan:
    `artifacts/agent_harness/v51/candidate_change_plan.json`
  - closeout runner result:
    `artifacts/agent_harness/v51/runner_result.json`
  - copied runner preview/provenance:
    `artifacts/agent_harness/v51/runner/`
  - verification result:
    `artifacts/agent_harness/v51/verification/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.json`
  - closeout evidence bundle:
    `artifacts/agent_harness/v51/evidence/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.json`
  - closeout evidence bundle hash sidecar:
    `artifacts/agent_harness/v51/evidence/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.sha256.json`
  - verifier provenance:
    `artifacts/agent_harness/v51/evidence/provenance/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS51_EDGES.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v51_closeout.json --baseline artifacts/quality_dashboard_v50_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v51_closeout.json --quality-baseline artifacts/quality_dashboard_v50_closeout.json --out-json artifacts/stop_gate/metrics_v51_closeout.json --out-md artifacts/stop_gate/report_v51_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python - <<'PY' ... generate v51 profile/registry/taskpack, closeout candidate plan, signed dry-run runner result, verification result, policy_recompute_result@1, evidence_inputs/*.json, and closeout evidence bundle/provenance from the v50 stop-gate artifacts, current compile/run/verify/write_closeout_evidence entrypoints, and the frozen v45 adapter registry ... PY`
  - `make closeout-lint`

## Exit-Criteria Check (vNext+51)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `Z1` merged with green CI | required | `pass` | PR `#251` merged; CI run `22772622530` is `success` |
| `Z2` merged with green CI | required | `pass` | PR `#252` merged; CI run `22773514719` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v50 and v51 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v50 and v51 keysets are exact-set equal (`metric_key_exact_set_equal_v50 = true`) |
| Deterministic cardinality continuity retained (`80`) | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| `policy_recompute_result@1` emitted and schema-valid | required | `pass` | `artifacts/agent_harness/v51/recompute/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.json` |
| Exact-match subject remains frozen to passed/issues/exit_status | required | `pass` | `comparison_subject_fields = ["passed", "issues", "exit_status"]` in recompute artifact and v34c evidence |
| Runner reason and line-range fields remain non-authoritative | required | `pass` | `runner_reason_line_range_non_authoritative = true` in `v34c_policy_recompute_evidence_v51.json` |
| Allowed issue-code set remains frozen and exact | required | `pass` | `allowed_issue_codes_closed_exact = true` in `v34c_policy_recompute_evidence_v51.json` |
| Canonical `v34c` evidence block emitted and hash-bound | required | `pass` | `policy_recompute_result_hash = 1e55b36abd3405d38f42da8456e8b8090310ac85844867212b5e94e1624b8688` in `v34c_policy_recompute_evidence_v51.json` and referenced recompute artifact |
| Duplicate issue tuples are rejected fail closed | required | `pass` | duplicate tuple rejection is enforced in `packages/adeu_agent_harness/src/adeu_agent_harness/policy_recompute.py` and guarded in `packages/adeu_agent_harness/tests/test_taskpack_runner.py` |
| Recompute mismatch fails closed in verifier lane | required | `pass` | guard test `test_verify_taskpack_run_fails_closed_on_policy_recompute_mismatch_after_emission` remains green in `packages/adeu_agent_harness/tests/test_taskpack_verifier.py` |
| Recompute artifact still emits on mismatch paths | required | `pass` | mismatch guard test and runner-policy-failure guard suite remain green in `packages/adeu_agent_harness/tests/test_taskpack_verifier.py` |
| No success-class verification result survives recompute mismatch | required | `pass` | mismatch guard test confirms verifier fails before any success-class verification result artifact remains |
| No boundary-release expansion introduced | required | `pass` | v51 scope remains verifier-lane `V34-C` only |

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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v50_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v51_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v50 Baseline vs v51 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+50",
  "current_arc": "vNext+51",
  "baseline_source": "artifacts/stop_gate/report_v50_closeout.md",
  "current_source": "artifacts/stop_gate/report_v51_closeout.md",
  "baseline_elapsed_ms": 100,
  "current_elapsed_ms": 93,
  "delta_ms": -7,
  "notes": "v51 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+50` baseline | `artifacts/stop_gate/metrics_v50_closeout.json` | `22` | `78` | `100` | `68230` | `204690` | `true` | `true` |
| `vNext+51` closeout | `artifacts/stop_gate/metrics_v51_closeout.json` | `22` | `78` | `93` | `68230` | `204690` | `true` | `true` |

## V34-C Policy Recompute Evidence

```json
{
  "schema": "v34c_policy_recompute_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS51.md#v34c_policy_recompute_contract@1",
  "recompute_entrypoint": "adeu_agent_harness.policy_recompute.recompute_policy_validation",
  "shared_recompute_engine_used": "adeu_agent_harness.policy_recompute.recompute_policy_validation",
  "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "policy_recompute_result_path": "artifacts/agent_harness/v51/recompute/3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f_fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab.json",
  "policy_recompute_result_hash": "1e55b36abd3405d38f42da8456e8b8090310ac85844867212b5e94e1624b8688",
  "comparison_subject_fields": [
    "passed",
    "issues",
    "exit_status"
  ],
  "exit_status_subject_policy": "runner_policy_verdict_status_under_frozen_validator_scope_not_verifier_process_exit_code",
  "issue_tuple_fields": [
    "issue_code",
    "target_path",
    "hunk_index"
  ],
  "issue_tuple_order_policy": "lexicographic_over_issue_code_target_path_hunk_index",
  "issues_representation_policy": "lexicographically_sorted_unique_issue_tuple_list_with_repo_relative_posix_target_paths",
  "duplicate_issue_tuples_forbidden": true,
  "allowed_issue_codes": [
    "allowlist_violation",
    "dry_run_subprocess_execution_detected",
    "forbidden_operation_kind",
    "forbidden_path_violation",
    "model_suggested_command_execution_detected"
  ],
  "allowed_issue_codes_closed_exact": true,
  "candidate_change_plan_binding_policy": "recompute_binds_to_runner_recorded_canonical_candidate_change_plan_hash_runner_result_dry_run_supplies_execution_mode_only",
  "runner_policy_failure_input_materialization_required": true,
  "runner_reason_line_range_non_authoritative": true,
  "mismatch_fail_closed": true,
  "exact_match_requires_empty_deltas": true,
  "policy_recompute_result_emitted": true,
  "typed_diff_summary_emitted": true,
  "success_class_verification_result_forbidden_on_mismatch": true,
  "verification_passed": true,
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v50": true,
  "notes": "v51 Z1/Z2 merged with shared policy recompute emission, verifier mismatch fail-closed enforcement, and canonical recompute evidence integration on main."
}
```

## Policy Recompute Result (Exact-Match Closeout Run)

```json
{
  "schema": "policy_recompute_result@1",
  "taskpack_manifest_hash": "3128cc9739666fbb04b57698816410a9d51cec6a1c7c535965ed9dcc9936298f",
  "candidate_change_plan_hash": "fdeccd2fa768f2f4956158aec542d20161ecaba2d8ff4f8a79e66a91a943f0ab",
  "runner_provenance_hash": "f24dfffe8a491545e111199d22cf9513998970e39ec09c67def3d3c503ab98e9",
  "dry_run": true,
  "shared_recompute_engine": "adeu_agent_harness.policy_recompute.recompute_policy_validation",
  "comparison_subject_fields": [
    "passed",
    "issues",
    "exit_status"
  ],
  "issue_tuple_fields": [
    "issue_code",
    "target_path",
    "hunk_index"
  ],
  "issue_tuple_order_policy": "lexicographic_over_issue_code_target_path_hunk_index",
  "issues_representation_policy": "lexicographically_sorted_unique_issue_tuple_list_with_repo_relative_posix_target_paths",
  "allowed_issue_codes": [
    "allowlist_violation",
    "dry_run_subprocess_execution_detected",
    "forbidden_operation_kind",
    "forbidden_path_violation",
    "model_suggested_command_execution_detected"
  ],
  "typed_diff_summary_fields": [
    "exact_match",
    "mismatch_fields",
    "runner_only_issues",
    "recompute_only_issues"
  ],
  "runner_outcome": {
    "passed": true,
    "issues": [],
    "exit_status": "success"
  },
  "recompute_outcome": {
    "passed": true,
    "issues": [],
    "exit_status": "success"
  },
  "typed_diff_summary": {
    "exact_match": true,
    "mismatch_fields": [],
    "runner_only_issues": [],
    "recompute_only_issues": []
  },
  "result_hash": "1e55b36abd3405d38f42da8456e8b8090310ac85844867212b5e94e1624b8688"
}
```

## Recommendation (Post v51)

- gate decision:
  - `GO_VNEXT_PLUS52_PLANNING_DRAFT`
- rationale:
  - v51 closes the verifier-lane `V34-C` baseline with shared canonical recompute
    emission, mismatch fail-closed behavior, and canonical `v34c` evidence integrated on
    `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout
    evidence.
  - future planning no longer needs to treat verifier-lane runner-trust closure as a
    missing baseline.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`,
   `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`, and
   `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md` from a fresh post-v51 planning pass.
2. Keep v51 closeout artifacts stable; rerun closeout commands only under the frozen
   deterministic env contract.
3. Carry only explicit follow-on paths into future planning:
   broader policy recomputation beyond the current runner validator,
   packaging-surface recomputation beyond verifier-lane comparison,
   `V34-D` retry-context automation,
   and remote/enclave follow-on lanes under explicit future lock text.
