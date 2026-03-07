# Draft Stop-Gate Decision (Post vNext+52)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`

Status: draft decision note (post-hoc closeout capture, March 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS52.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v52_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+52` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md`.
- This note captures `V34-D` advisory retry-context feeder closeout evidence only; it does
  not authorize `V34-E`..`V34-G` behavior release by itself.
- Shared canonical retry-context feeder generation, deterministic
  `retry_context_feeder_result@1` and `retry_context_sanitization_profile@1` emission,
  advisory-only posture, and cumulative closeout evidence integration remain
  artifact-authoritative, deterministic, and fail-closed under frozen lock text.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `99d86b473ad47c7e56f324fd7a44ae84b8ccfeea`
- arc-completion CI runs:
  - PR `#253`
    - Run ID: `22781621715`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/22781621715`
    - conclusion: `success`
  - PR `#254`
    - Run ID: `22785782330`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/22785782330`
    - conclusion: `success`
- merged implementation PRs:
  - `#253` (`contracts: add v34d retry-context feeder baseline`)
  - `#254` (`tests: add v34d retry-context evidence and advisory guards`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v52_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v52_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v52_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/runtime_observability_comparison_v52.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/metric_key_continuity_assertion_v52.json`
  - policy recompute evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/v34c_policy_recompute_evidence_v52.json`
  - retry-context evidence input:
    `artifacts/agent_harness/v52/evidence_inputs/v34d_retry_context_evidence_v52.json`
  - retry-context feeder artifact:
    `artifacts/agent_harness/v52/retry_context/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_837b83267ebbd0531dc9ea75c1c18965c23bb598f582416dce6f493aac3bc3e8.json`
  - sanitization profile artifact:
    `artifacts/agent_harness/v52/retry_context/retry_context_sanitization_profile.json`
- supporting deterministic verifier/evidence artifacts (reproducible):
  - closeout profile:
    `artifacts/agent_harness/v52/profiles/v52_closeout_profile.json`
  - taskpack profile registry:
    `artifacts/agent_harness/v52/taskpack_profile_registry.json`
  - compiled closeout taskpack:
    `artifacts/agent_harness/v52/taskpacks/v41/v52_closeout/`
  - closeout candidate change plan:
    `artifacts/agent_harness/v52/candidate_change_plan.json`
  - retry-context seed candidate change plan:
    `artifacts/agent_harness/v52/candidate_change_plan_retry_context.json`
  - closeout runner result:
    `artifacts/agent_harness/v52/runner_result.json`
  - retry-context seed runner result:
    `artifacts/agent_harness/v52/runner_result_policy_failure.json`
  - copied runner preview/provenance/rejection artifacts:
    `artifacts/agent_harness/v52/runner/`
  - signing handoff artifacts:
    `artifacts/agent_harness/v52/test_signing/`
  - verification result:
    `artifacts/agent_harness/v52/verification/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_59b1d0cb1087b70f3fd181b8819db2ac20b3b60e4ba0b184b416ccebbdaecdf7.json`
  - policy recompute artifact:
    `artifacts/agent_harness/v52/recompute/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_59b1d0cb1087b70f3fd181b8819db2ac20b3b60e4ba0b184b416ccebbdaecdf7.json`
  - closeout evidence bundle:
    `artifacts/agent_harness/v52/evidence/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_59b1d0cb1087b70f3fd181b8819db2ac20b3b60e4ba0b184b416ccebbdaecdf7.json`
  - closeout evidence bundle hash sidecar:
    `artifacts/agent_harness/v52/evidence/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_59b1d0cb1087b70f3fd181b8819db2ac20b3b60e4ba0b184b416ccebbdaecdf7.sha256.json`
  - verifier provenance:
    `artifacts/agent_harness/v52/evidence/provenance/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_59b1d0cb1087b70f3fd181b8819db2ac20b3b60e4ba0b184b416ccebbdaecdf7.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS52_EDGES.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v52_closeout.json --baseline artifacts/quality_dashboard_v51_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v52_closeout.json --quality-baseline artifacts/quality_dashboard_v51_closeout.json --out-json artifacts/stop_gate/metrics_v52_closeout.json --out-md artifacts/stop_gate/report_v52_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python - <<'PY' ... generate v52 profile/registry/taskpack, deterministic signing handoff, success + rejection runner artifacts, verification result, policy_recompute_result@1, retry_context_feeder_result@1, retry_context_sanitization_profile@1, evidence_inputs/*.json, and closeout evidence bundle/provenance from the v51 stop-gate artifacts, current compile/run/verify/retry_context/write_closeout_evidence entrypoints, and the frozen v45 adapter registry ... PY`
  - `make closeout-lint`

## Exit-Criteria Check (vNext+52)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `A1` merged with green CI | required | `pass` | PR `#253` merged; CI run `22781621715` is `success` |
| `A2` merged with green CI | required | `pass` | PR `#254` merged; CI run `22785782330` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v51 and v52 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v51 and v52 keysets are exact-set equal (`metric_key_exact_set_equal_v51 = true`) |
| Deterministic cardinality continuity retained (`80`) | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| `retry_context_feeder_result@1` emitted and schema-valid | required | `pass` | `artifacts/agent_harness/v52/retry_context/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_837b83267ebbd0531dc9ea75c1c18965c23bb598f582416dce6f493aac3bc3e8.json` |
| `retry_context_sanitization_profile@1` emitted and schema-valid | required | `pass` | `artifacts/agent_harness/v52/retry_context/retry_context_sanitization_profile.json` |
| Advisory-only posture retained | required | `pass` | `advisory_only_non_authoritative = true` in retry-context result/profile/evidence payloads |
| Raw repo-content inclusion remains forbidden | required | `pass` | `raw_repo_file_content_forbidden = true` in retry-context result/profile/evidence payloads |
| Automatic retry dispatch remains out of scope | required | `pass` | `automatic_retry_dispatch_forbidden = true` in retry-context result/profile/evidence payloads |
| Canonical `v34d` evidence block emitted and hash-bound | required | `pass` | `retry_context_feeder_result_hash = 612cde48cf8f83f916d47d5055426bcadab805d2bb60ca8bcf0c7c96a97add28` and `sanitization_profile_hash = 40cf4ca5ae3631afda7c7221470cdfd45cd4e88b848db40cfae8a220bdd366ee` in `v34d_retry_context_evidence_v52.json` |
| No boundary-release expansion introduced | required | `pass` | v52 scope remains advisory `V34-D` only |

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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v51_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v52_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v51 Baseline vs v52 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+51",
  "current_arc": "vNext+52",
  "baseline_source": "artifacts/stop_gate/report_v51_closeout.md",
  "current_source": "artifacts/stop_gate/report_v52_closeout.md",
  "baseline_elapsed_ms": 93,
  "current_elapsed_ms": 99,
  "delta_ms": 6,
  "notes": "v52 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+51` baseline | `artifacts/stop_gate/metrics_v51_closeout.json` | `22` | `78` | `93` | `68230` | `204690` | `true` | `true` |
| `vNext+52` closeout | `artifacts/stop_gate/metrics_v52_closeout.json` | `22` | `78` | `99` | `68230` | `204690` | `true` | `true` |

## V34-D Retry-Context Evidence

```json
{
  "schema": "v34d_retry_context_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS52.md#v34d_retry_context_contract@1",
  "feeder_entrypoint": "python -m adeu_agent_harness.retry_context",
  "shared_feeder_engine_used": "adeu_agent_harness.retry_context.generate_retry_context",
  "shared_feeder_engine_identifier": "v34d_retry_context_feeder_engine@1:adeu_agent_harness.retry_context.generate_retry_context",
  "retry_context_feeder_result_path": "artifacts/agent_harness/v52/retry_context/ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944_837b83267ebbd0531dc9ea75c1c18965c23bb598f582416dce6f493aac3bc3e8.json",
  "retry_context_feeder_result_hash": "612cde48cf8f83f916d47d5055426bcadab805d2bb60ca8bcf0c7c96a97add28",
  "sanitization_profile_path": "artifacts/agent_harness/v52/retry_context/retry_context_sanitization_profile.json",
  "sanitization_profile_hash": "40cf4ca5ae3631afda7c7221470cdfd45cd4e88b848db40cfae8a220bdd366ee",
  "source_rejection_diagnostic_schema": "candidate_change_plan_rejection_diagnostic@1",
  "policy_source_closed_inherited_surface": true,
  "runner_result_semantic_input_forbidden": true,
  "advisory_only_non_authoritative": true,
  "automatic_retry_dispatch_forbidden": true,
  "downstream_diagnostic_aggregation_forbidden": true,
  "policy_success_explicit_request_without_diagnostic_fails_closed": true,
  "raw_repo_file_content_forbidden": true,
  "duplicate_issue_tuples_forbidden": true,
  "excerpt_bounds_enforced": true,
  "overflow_policy": "deterministic_truncation_under_frozen_profile",
  "missing_excerpt_source_policy": "unresolvable_candidate_plan_excerpt_emits_null_typed_excerpt_and_no_repo_fallback",
  "total_output_bound_enforced": true,
  "control_marker_neutralization_enforced": true,
  "deterministic_issue_order_enforced": true,
  "verification_passed": true,
  "verification_passed_policy": "true_means_feeder_generation_guards_and_closeout_validation_passed_not_policy_validation_packaging_validation_or_model_success",
  "success_path_absence_without_request_allowed": true,
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v51": true,
  "notes": "v52 A1/A2 merged with deterministic advisory retry-context feeder artifacts and canonical v34d evidence integration on main."
}
```

## Retry-Context Feeder Result (Advisory Rejection-Path Closeout Run)

```json
{
  "schema": "retry_context_feeder_result@1",
  "taskpack_manifest_hash": "ee0acc17f3994c841e84bd53da218e13d1e2318c9bf8cdaffbe6a4cc2655f944",
  "candidate_change_plan_hash": "837b83267ebbd0531dc9ea75c1c18965c23bb598f582416dce6f493aac3bc3e8",
  "runner_result_hash": "923829ba3b88ed012dc5c738b9b4066f59d9ad5d86d8cd8581d96db7c10bf284",
  "rejection_diagnostic_hash": "d8352f19da48eaa6af9dab8718e6c6ba93c814f9fdccebce39a8911079de4c1c",
  "source_rejection_diagnostic_schema": "candidate_change_plan_rejection_diagnostic@1",
  "shared_feeder_engine": "adeu_agent_harness.retry_context.generate_retry_context",
  "shared_feeder_engine_identifier": "v34d_retry_context_feeder_engine@1:adeu_agent_harness.retry_context.generate_retry_context",
  "advisory_only_non_authoritative": true,
  "automatic_retry_dispatch_forbidden": true,
  "downstream_diagnostic_aggregation_forbidden": true,
  "raw_repo_file_content_forbidden": true,
  "target_path_normalization_policy": "repo_relative_posix",
  "policy_source_policy": "closed_inherited_surface_from_candidate_change_plan_rejection_diagnostic_contract_no_v52_expansion",
  "deterministic_issue_order_policy": "lexicographic_over_issue_code_target_path_hunk_index_policy_source",
  "overflow_policy": "deterministic_truncation_under_frozen_profile",
  "missing_excerpt_source_policy": "unresolvable_candidate_plan_excerpt_emits_null_typed_excerpt_and_no_repo_fallback",
  "policy_success_absence_without_request_allowed": true,
  "sanitization_profile_path": "artifacts/agent_harness/v52/retry_context/retry_context_sanitization_profile.json",
  "sanitization_profile_hash": "40cf4ca5ae3631afda7c7221470cdfd45cd4e88b848db40cfae8a220bdd366ee",
  "issue_count_input": 2,
  "issue_count_emitted": 2,
  "issue_count_truncated": false,
  "total_output_chars_used": 98,
  "result_hash": "612cde48cf8f83f916d47d5055426bcadab805d2bb60ca8bcf0c7c96a97add28"
}
```

## Recommendation (Post v52)

- gate decision:
  - `GO_VNEXT_PLUS53_PLANNING_DRAFT`
- rationale:
  - v52 closes the advisory `V34-D` retry-context feeder baseline with deterministic
    feeder/profile artifacts, advisory-only posture, and canonical `v34d` evidence
    integrated on `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout.
