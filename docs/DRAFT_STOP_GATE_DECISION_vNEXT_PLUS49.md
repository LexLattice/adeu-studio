# Draft Stop-Gate Decision (Planned vNext+49)

This note records the draft stop-gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`

Status: draft decision note (pre-start threshold scaffold, March 6, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS49.md",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": true,
  "authoritative_scope": "v49_exit_criteria_and_closeout_placeholders",
  "required_in_closeout": true,
  "all_passed": null,
  "notes": "This draft captures pre-start thresholds and required closeout evidence only. Final decision values must be written after implementation and closeout."
}
```

## Decision Guardrail (Frozen)

- This draft does not certify `vNext+49` as passed.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`.
- This note predefines the v49 exit criteria only.
- Any recommendation about `vNext+50` is non-binding until `all_passed = true` for the
  final v49 closeout evidence.

## Planned Evidence Source

- CI workflow: `ci` on `main`
- expected implementation PRs:
  - PR `TBD-1`: `contracts: complete v34a downstream signing handoff in harness pipeline`
  - PR `TBD-2`: `tests: add v49 handoff/evidence guards and repair continuity sentinel`
- expected deterministic closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v49_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v49_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v49_closeout.md`
  - expected deterministic closeout evidence input artifact:
    `artifacts/agent_harness/v49/evidence_inputs/runtime_observability_comparison_v49.json`
  - expected deterministic closeout evidence input artifact:
    `artifacts/agent_harness/v49/evidence_inputs/metric_key_continuity_assertion_v49.json`
  - expected deterministic closeout evidence input artifact:
    `artifacts/agent_harness/v49/evidence_inputs/v34a_handoff_completion_evidence_v49.json`

Evidence-input note:

- the `artifacts/agent_harness/v49/evidence_inputs/*.json` files listed here are planned
  deterministic inputs to the closeout writer and do not, by themselves, constitute final
  closeout proof until materialized and validated during v49 closeout.

## Exit-Criteria Check (Planned vNext+49)

| Criterion | Threshold | Planned Result | Required Evidence |
|---|---|---|---|
| `X3` merged with green CI | required | `pending` | merged PR + green `ci` |
| `X4` merged with green CI | required | `pending` | merged PR + green `ci` |
| Stop-gate schema-family continuity retained | required | `pending` | `schema = "stop_gate_metrics@1"` in v48 and v49 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pending` | v48 and v49 keysets are exact-set equal |
| Deterministic cardinality continuity retained | required | `pending` | metric-key cardinality computed from `metrics` keys remains `80` |
| Downstream signature-result handoff enforced in the harness path | required | `pending` | runner/verifier/packaging guards + closeout evidence |
| Shared binding validator use and required binding-check proof materialized in closeout evidence | required | `pending` | handoff completion evidence includes validator identity, binding field list, and `verified_required` |
| Detached or stale signing-result acceptance blocked fail closed | required | `pending` | deterministic rejection coverage and closeout evidence |
| Current taskpack snapshot drift after preflight is rejected fail closed | required | `pending` | deterministic mismatch coverage over recomputed manifest/bundle hashes in downstream paths |
| Canonical closeout includes `v34a_handoff_completion_evidence@1` | required | `pending` | `artifacts/agent_harness/v49/evidence_inputs/v34a_handoff_completion_evidence_v49.json` |
| Historical v47-to-v48 continuity sentinel repaired | required | `pending` | deterministic test coverage over distinct v47/v48 artifacts with self-compare rejection |
| Baseline/current continuity self-compare configuration rejected fail closed | required | `pending` | deterministic guard coverage proving baseline and current metrics artifacts must differ |
| No boundary-release expansion introduced | required | `pending` | v49 scope remains `V34-A` completion only |

Summary placeholder:

- `schema = "stop_gate_metrics@1"`
- `valid = null`
- `all_passed = null`
- `issues = null`
- `derived_cardinality = null`

## Planned Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_metrics_artifact": "artifacts/stop_gate/metrics_v48_closeout.json",
  "current_metrics_artifact": "artifacts/stop_gate/metrics_v49_closeout.json",
  "expected_relation": "exact_keyset_equality",
  "metric_key_exact_set_equal_v48": null,
  "metric_key_cardinality": null
}
```

## Planned Runtime Observability Comparison (v48 Baseline vs v49 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "baseline_arc": "vNext+48",
  "current_arc": "vNext+49",
  "baseline_source": "artifacts/stop_gate/report_v48_closeout.md",
  "current_source": "artifacts/stop_gate/report_v49_closeout.md",
  "baseline_elapsed_ms": null,
  "current_elapsed_ms": null,
  "delta_ms": null,
  "notes": "v49 closeout remains informational-only for timing and runtime byte observability under frozen stop-gate semantics."
}
```

## Planned V34-A Handoff Completion Evidence

```json
{
  "schema": "v34a_handoff_completion_evidence@1",
  "phase": "pre_start_threshold_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md#v34a_handoff_completion_contract@1",
  "preflight_entrypoint": "python -m adeu_agent_harness.verify_taskpack_signature",
  "runner_entrypoint": "python -m adeu_agent_harness.run_taskpack",
  "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
  "packaging_entrypoints": [
    "python -m adeu_agent_harness.package_ux_integrated",
    "python -m adeu_agent_harness.package_ux_standalone"
  ],
  "shared_binding_validator_used": null,
  "binding_fields_verified": null,
  "verified_required": null,
  "signature_result_consumed_by_runner": null,
  "signature_result_consumed_by_verifier": null,
  "signature_result_consumed_by_packaging": null,
  "current_taskpack_snapshot_binding_enforced": null,
  "detached_user_supplied_handoff_forbidden": null,
  "historical_v47_to_v48_continuity_guard_repaired": null,
  "verification_passed": null,
  "metric_key_cardinality": null,
  "metric_key_exact_set_equal_v48": null,
  "notes": "Planned deterministic evidence input only. Final values must be populated from v49 closeout evidence under the v34a_handoff_completion_contract@1 requirements."
}
```

## Recommendation (Pre-Start v49)

- gate decision:
  - `HOLD_VNEXT_PLUS50_PENDING_V49_CLOSEOUT`
- rationale:
  - v49 is a completion/hardening slice, not a forward scope expansion slice;
  - `V34-B` should not be selected until the v48 signing handoff/evidence gaps are closed;
  - final go/no-go can only be set after deterministic closeout evidence is written.

## Suggested Next Artifacts

1. Review and refine `docs/LOCKED_CONTINUATION_vNEXT_PLUS49.md`.
2. Implement `X3` and `X4` in the two PRs defined by the lock.
3. Replace `pending` placeholders in this note only after merged implementation and closeout
   evidence exist on `main`.
