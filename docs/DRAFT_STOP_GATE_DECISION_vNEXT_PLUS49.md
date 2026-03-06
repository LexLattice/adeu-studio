# Draft Stop-Gate Decision (Post vNext+49)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`

Status: draft decision note (post-hoc closeout capture, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v49_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+49` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`.
- This note captures `V34-A` completion closeout evidence only; it does not authorize
  `V34-B`..`V34-G` behavior release by itself.
- Downstream signing handoff and handoff-completion evidence remain artifact-authoritative,
  deterministic, and fail-closed under frozen lock text.
- Runtime-observability comparison row remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `0d753951b9db383c16d6c24cb926df9320ee1823`
- arc-completion CI run:
  - Run ID: `22758852869`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22758852869`
  - conclusion: `success`
- merged implementation PRs:
  - `#247` (`contracts: complete v34a downstream signing handoff in harness pipeline`)
  - `#248` (`tests: add v49 handoff/evidence guards and repair continuity sentinel`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v49_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v49_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v49_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v49/evidence_inputs/runtime_observability_comparison_v49.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v49/evidence_inputs/metric_key_continuity_assertion_v49.json`
  - handoff-completion evidence input:
    `artifacts/agent_harness/v49/evidence_inputs/v34a_handoff_completion_evidence_v49.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS49_EDGES.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v49_closeout.json --baseline artifacts/quality_dashboard_v48_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v49_closeout.json --quality-baseline artifacts/quality_dashboard_v48_closeout.json --out-json artifacts/stop_gate/metrics_v49_closeout.json --out-md artifacts/stop_gate/report_v49_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/urm_runtime/src .venv/bin/python - <<'PY' ... write v49 evidence_inputs/*.json from v48/v49 stop-gate artifacts and write_closeout_evidence constants ... PY`

## Exit-Criteria Check (vNext+49)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `X3` merged with green CI | required | `pass` | PR `#247` merged; CI run `22743936500` is `success` |
| `X4` merged with green CI | required | `pass` | PR `#248` merged; CI run `22758852869` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v48 and v49 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v48 and v49 keysets are exact-set equal (`added_keys = []`, `removed_keys = []`) |
| Deterministic cardinality continuity retained | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| Downstream signature-result handoff enforced in the harness path | required | `pass` | PR `#247` merged; runner/verifier/packaging paths now consume the downstream handoff contract under shared validation |
| Shared binding validator use and required binding-check proof materialized in closeout evidence | required | `pass` | `artifacts/agent_harness/v49/evidence_inputs/v34a_handoff_completion_evidence_v49.json` |
| Detached or stale signing-result acceptance blocked fail closed | required | `pass` | merged X3/X4 guard suites and v49 handoff-completion evidence confirm fail-closed posture |
| Current taskpack snapshot drift after preflight is rejected fail closed | required | `pass` | downstream snapshot-binding guard coverage is green in the v49 verifier/packaging suites |
| Canonical closeout includes `v34a_handoff_completion_evidence@1` | required | `pass` | `artifacts/agent_harness/v49/evidence_inputs/v34a_handoff_completion_evidence_v49.json` |
| Historical v47-to-v48 continuity sentinel repaired | required | `pass` | `packages/adeu_agent_harness/tests/test_taskpack_signature.py` now compares distinct v47/v48 artifacts and rejects self-compare configuration |
| Baseline/current continuity self-compare configuration rejected fail closed | required | `pass` | targeted v49 harness rerun (`65` passing tests) includes explicit self-compare rejection coverage |
| No boundary-release expansion introduced | required | `pass` | v49 scope remains `V34-A` completion only |

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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v48_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v49_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v48 Baseline vs v49 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+48",
  "current_arc": "vNext+49",
  "baseline_source": "artifacts/stop_gate/report_v48_closeout.md",
  "current_source": "artifacts/stop_gate/report_v49_closeout.md",
  "baseline_elapsed_ms": 111,
  "current_elapsed_ms": 97,
  "delta_ms": -14,
  "notes": "v49 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+48` baseline | `artifacts/stop_gate/metrics_v48_closeout.json` | `22` | `78` | `111` | `68230` | `204690` | `true` | `true` |
| `vNext+49` closeout | `artifacts/stop_gate/metrics_v49_closeout.json` | `22` | `78` | `97` | `68230` | `204690` | `true` | `true` |

## V34-A Handoff Completion Evidence

```json
{
  "schema": "v34a_handoff_completion_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md#v34a_handoff_completion_contract@1",
  "preflight_entrypoint": "python -m adeu_agent_harness.verify_taskpack_signature",
  "runner_entrypoint": "python -m adeu_agent_harness.run_taskpack",
  "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
  "packaging_entrypoints": [
    "python -m adeu_agent_harness.package_ux_integrated",
    "python -m adeu_agent_harness.package_ux_standalone"
  ],
  "shared_binding_validator_used": "packages/adeu_agent_harness.verify_taskpack_signature.validate_signature_verification_result_for_downstream",
  "binding_fields_verified": [
    "taskpack_manifest_hash",
    "taskpack_bundle_hash",
    "signature_envelope_hash",
    "trust_anchor_registry_hash",
    "verification_reference_time_utc",
    "preflight_invocation_binding_hash",
    "signer_key_id",
    "algorithm",
    "verified"
  ],
  "verified_required": true,
  "signature_result_consumed_by_runner": true,
  "signature_result_consumed_by_verifier": true,
  "signature_result_consumed_by_packaging": true,
  "current_taskpack_snapshot_binding_enforced": true,
  "detached_user_supplied_handoff_forbidden": true,
  "historical_v47_to_v48_continuity_guard_repaired": true,
  "verification_passed": true,
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v48": true,
  "notes": "v49 X3/X4 merged with downstream handoff enforcement, canonical handoff-completion evidence integration, and repaired v47-to-v48 continuity self-compare rejection on main."
}
```

## Recommendation (Post v49)

- gate decision:
  - `GO_VNEXT_PLUS50_PLANNING_DRAFT`
- rationale:
  - v49 closes `V34-A` on the real downstream harness path rather than only at the
    preflight/helper layer.
  - canonical closeout evidence now carries `v34a_handoff_completion_evidence@1` under the
    frozen v49 contract.
  - no continuity, schema-family, or metric-key regressions were observed in closeout
    evidence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS50.md`,
   `docs/ASSESSMENT_vNEXT_PLUS50_EDGES.md`, and
   `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS50.md` from a fresh post-v49 planning pass.
2. Keep v49 closeout artifacts stable; rerun closeout commands only under the frozen
   deterministic env contract.
3. Carry only explicit deferred paths (`V34-B`..`V34-G`, crypto portability, remote/enclave
   execution) into future planning rather than re-opening v49 closure items.
