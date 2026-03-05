# Draft Stop-Gate Decision (Pre vNext+46)

This note records the pre-implementation decision posture for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`

Status: draft decision note (planning start, March 5, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+46` implementation-start posture only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`.
- This note captures `V33-C` (`U1`/`U2`) planning intent only; it does not authorize `V33-D` behavior release.
- v46 verifier remains auditor-only: policy validation recomputation is out of scope and forbidden in this arc.
- Runtime-observability comparison row is required closeout evidence and remains informational-only in this arc unless explicitly re-locked.

## Planning Evidence Source

- planning baseline:
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v7.md`
- prior closed lock:
  - `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`
- prior closeout decision:
  - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md`
- v45 closeout artifacts (baseline for v46 comparisons):
  - `artifacts/quality_dashboard_v45_closeout.json`
  - `artifacts/stop_gate/metrics_v45_closeout.json`
  - `artifacts/stop_gate/report_v45_closeout.md`

## Entry-Criteria Check (vNext+46 Start)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| v45 closeout decision exists and is green | required | `pass` | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS45.md` (`all_passed = true`) |
| v45 stop-gate schema family is stable | required | `pass` | `schema = "stop_gate_metrics@1"` in `artifacts/stop_gate/metrics_v45_closeout.json` |
| v45 metric-key cardinality baseline is stable | required | `pass` | derived key cardinality = `80` in `artifacts/stop_gate/metrics_v45_closeout.json` |
| v46 scope remains `V33-C` only | required | `pass` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md` scope/locks |
| no boundary-release expansion introduced at planning start | required | `pass` | v46 lock keeps `L2` release unauthorized |

## Planned Exit-Criteria Check (vNext+46 Closeout)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `U1` merged with green CI | required | `pending` | PR + CI run IDs to populate at closeout |
| `U2` merged with green CI | required | `pending` | PR + CI run IDs to populate at closeout |
| Stop-gate schema-family continuity retained | required | `pending` | `stop_gate_metrics@1` in v45/v46 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pending` | exact-set equality v45 vs v46 (`added_keys=[]`, `removed_keys=[]`) |
| Deterministic cardinality continuity retained | required | `pending` | metric key cardinality computed from `metrics` keys is `80 -> 80` |
| V33-C verifier/evidence artifacts are deterministic and fail-closed | required | `pending` | run1/run2 verifier outputs + evidence/provenance parity |
| Dual-entrypoint control flow contract is enforced | required | `pending` | default `verify -> evidence_write`; independent writer rerun only with prior verified-result artifact |
| Hash-match cross-check semantics are recomputation-based | required | `pending` | verifier recomputes canonical artifact hashes; recorded hash fields alone are non-authoritative |
| Evidence bundle hash subject canonicalization is frozen and enforced | required | `pending` | each evidence block/diagnostic uses `canonical_json` before bundle hash assembly |
| Verification failure emits no partial closeout evidence | required | `pending` | failed verify fixture yields no closeout blocks (rejections-only artifacts allowed) |
| Verifier diagnostics namespace mapping is enforced | required | `pending` | emitted codes are `AHK46xx` and registry-mapped subset of `AHK[0-9]{4}` |
| Verifier diagnostics `policy_source` enum is enforced | required | `pending` | diagnostics `policy_source` values are from frozen v46 closed enum only |
| Historical continuity posture remains green | required | `pending` | v46 closeout `issues=[]`, `valid=true`, `all_passed=true` |
| No boundary-release expansion introduced | required | `pending` | v46 scope remains `V33-C` only (`U1`/`U2`) |

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v45_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v46_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v45 Baseline vs v46 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+45",
  "current_arc": "vNext+46",
  "baseline_source": "artifacts/stop_gate/report_v45_closeout.md",
  "current_source": "artifacts/stop_gate/report_v46_closeout.md",
  "baseline_elapsed_ms": "TBD_CLOSEOUT",
  "current_elapsed_ms": "TBD_CLOSEOUT",
  "delta_ms": "TBD_CLOSEOUT",
  "notes": "Populate during v46 closeout. Runtime observability remains informational-only under v46 locks."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+45` baseline | `artifacts/stop_gate/metrics_v45_closeout.json` | `22` | `78` | `93` | `68230` | `204690` | `true` | `true` |
| `vNext+46` closeout | `artifacts/stop_gate/metrics_v46_closeout.json` | `TBD_CLOSEOUT` | `TBD_CLOSEOUT` | `TBD_CLOSEOUT` | `TBD_CLOSEOUT` | `TBD_CLOSEOUT` | `TBD_CLOSEOUT` | `TBD_CLOSEOUT` |

## V33-C Verifier Wiring Evidence

```json
{
  "schema": "v33c_verifier_wiring_evidence@1",
  "verifier_entrypoint": "python -m adeu_agent_harness.verify_taskpack_run",
  "evidence_writer_entrypoint": "python -m adeu_agent_harness.write_closeout_evidence",
  "execution_mode_default": "sequential_verify_then_evidence_write",
  "independent_evidence_writer_rerun": "allowed_only_with_prior_verified_result_artifact",
  "verified_result_artifact_schema": "taskpack_verification_result@1",
  "hash_match_semantics": "recompute_hash_from_canonical_artifact_payload_and_compare_to_recorded_hash_field",
  "writable_schema_allowlist": [
    "runtime_observability_comparison@1",
    "metric_key_continuity_assertion@1",
    "v33c_verifier_wiring_evidence@1"
  ],
  "canonical_serialization_policy": "canonical_json_recursive_required_for_all_evidence_blocks_and_rejection_diagnostics",
  "evidence_bundle_hash_subject_frozen": "TBD_CLOSEOUT",
  "diagnostic_code_prefix": "AHK46",
  "diagnostic_code_parent_namespace": "AHK[0-9]{4}",
  "diagnostic_namespace_mapping_enforced": "TBD_CLOSEOUT",
  "policy_source_enum_enforced": "TBD_CLOSEOUT",
  "verification_passed": "TBD_CLOSEOUT",
  "required_evidence_slots_filled": "TBD_CLOSEOUT",
  "required_violation_error_channel_enforced": "TBD_CLOSEOUT",
  "provenance_hash": "TBD_CLOSEOUT",
  "metric_key_cardinality": "TBD_CLOSEOUT",
  "metric_key_exact_set_equal_v45": "TBD_CLOSEOUT",
  "notes": "Populate with deterministic closeout evidence after v46 implementation merges."
}
```

## Recommendation (Pre v46)

- gate decision:
  - `GO_VNEXT_PLUS46_IMPLEMENTATION_DRAFT`
- rationale:
  - v45 closes `V33-B` with green continuity and deterministic runner evidence.
  - v46 lock scope is constrained to deterministic `V33-C` verifier/evidence lane only, preserving all stop-gate continuity locks.

## Suggested Next Artifacts

1. Implement `U1` (`V33-C` verifier/evidence writer) in a small green PR with fail-closed deterministic behavior.
2. Implement `U2` deterministic/fail-closed guard suite in a second green PR.
3. Replace all `TBD_CLOSEOUT` placeholders with concrete values only after v46 closeout artifacts are generated under frozen deterministic env settings.
4. Keep independent policy-recompute verifier logic deferred until a dedicated non-v46 lock explicitly authorizes zero-trust recomputation.
5. Keep automated rejection-feedback retry loop and remote attested verifier execution deferred until explicitly locked in later arcs.
