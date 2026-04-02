# Draft Stop-Gate Decision (Post vNext+114)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS114.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v114_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+114` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md`.
- This note captures bounded `V48-C` worker-envelope evidence only; it does not
  authorize replayable post-run conformance release, observed-action carrier release,
  signature-envelope redefinition, execution-result release, multi-worker topology,
  repo-wide orchestration, execution posture expansion, approval posture, waiver
  issuance, or deferral issuance by itself.
- Canonical `V48-C` release in `v114` is carried by the shipped
  `adeu_agent_harness` source, schema-export, deterministic fixtures, and targeted
  test surfaces plus the canonical `v48c_worker_execution_envelope_evidence@1`
  evidence input under `artifacts/agent_harness/v114/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#336` (`V48-C: add worker execution envelope surfaces`)
- arc-completion merge commit: `cf43eea67a928d7b3ad22614c388de652010301e`
- merged-at timestamp: `2026-04-02T22:04:36Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v114_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v114_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v114_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v114/evidence_inputs/metric_key_continuity_assertion_v114.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v114/evidence_inputs/runtime_observability_comparison_v114.json`
  - `V48-C` release evidence input:
    `artifacts/agent_harness/v114/evidence_inputs/v48c_worker_execution_envelope_evidence_v114.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v114/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS114_EDGES.md`

## Exit-Criteria Check (vNext+114)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V48-C` merged with green CI | required | `pass` | PR `#336`, merge commit `cf43eea67a928d7b3ad22614c388de652010301e`, checks `python/web/lean-formal = pass` |
| Released boundary-instance, attestation, and provenance surfaces ship with authoritative/mirror schema parity | required | `pass` | `packages/adeu_agent_harness/schema/task_run_boundary_instance.v1.json`, `packages/adeu_agent_harness/schema/worker_execution_attestation.v1.json`, `packages/adeu_agent_harness/schema/worker_execution_provenance.v1.json`, mirrored `spec/*.schema.json`, and parity coverage in `packages/adeu_agent_harness/tests/test_worker_execution_envelope_export_schema.py` |
| Accepted reference worker-envelope fixture replays deterministically | required | `pass` | committed reference fixtures under `packages/adeu_agent_harness/tests/fixtures/v48c/` and test `test_v48c_reference_worker_execution_envelope_replays_deterministically` |
| Every accepted envelope binds exactly one released compiled boundary, one repo ref, one task instance identity, and one worker subject/provider/model/adapter tuple | required | `pass` | cardinality and identity validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py`, committed reference fixtures, and tests `test_v48c_reference_worker_execution_envelope_replays_deterministically` plus `test_v48c_models_accept_committed_reference_payloads` |
| Worker provider/model identity remains explicit envelope-owned fact and is not inferred from attestation-provider identity | required | `pass` | provider/model vs attestation-provider checks in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py` and test `test_v48c_rejects_worker_provider_conflation_with_attestation_provider` |
| Released runner-result and runner-provenance support carriers remain explicit, required, and hash-coherent | required | `pass` | support-carrier validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py` and test `test_v48c_rejects_runner_provenance_hash_mismatch` |
| Any selected verifier-result or attestation-validator support carriers fail closed on missing required fields | required | `pass` | fail-closed carrier validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py` and tests `test_v48c_rejects_missing_verification_result_required_field`, `test_v48c_rejects_missing_attestation_verification_required_field`, and `test_v48c_rejects_missing_attestation_output_remote_fields` |
| Attestation carries explicit hash anchors over the consumed support chain | required | `pass` | `runner_provenance_hash`, `verification_result_hash`, and `attestation_validator_result_hash` in the released schema pair, committed reference fixture `packages/adeu_agent_harness/tests/fixtures/v48c/reference_worker_execution_attestation.json`, and deterministic replay coverage |
| `repo_ref` remains one exact execution repository identity coherent with the bound snapshot | required | `pass` | repo/snapshot identity validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py` and committed reference boundary-instance fixture |
| Provenance `emitted_artifact_refs` remain support-artifact outputs only rather than observed-action carriers | required | `pass` | released provenance schema pair, committed reference fixture `packages/adeu_agent_harness/tests/fixtures/v48c/reference_worker_execution_provenance.json`, and bounded emission logic in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py` |
| Raw `V48-A` / `V45` / `V47` bypass, prompt-authority drift, and stale compiled-boundary misuse fail closed | required | `pass` | source-kind and prompt-conflict guards in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py` and tests `test_v48c_rejects_raw_v48a_bypass` plus `test_v48c_rejects_prompt_authority_drift` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v114_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v114/evidence_inputs/metric_key_continuity_assertion_v114.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v114/evidence_inputs/runtime_observability_comparison_v114.json` |

## Stop-Gate Summary

```json
{
  "schema": "v114_closeout_stop_gate_summary@1",
  "arc": "vNext+114",
  "target_path": "V48-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v113": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 111,
  "runtime_observability_delta_ms": -14
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v113_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v114_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+113","current_arc":"vNext+114","baseline_source":"artifacts/stop_gate/report_v113_closeout.md","current_source":"artifacts/stop_gate/report_v114_closeout.md","baseline_elapsed_ms":125,"current_elapsed_ms":111,"delta_ms":-14,"notes":"v114 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V48-C worker-envelope lane: one canonical task_run_boundary_instance@1, one canonical worker_execution_attestation@1, one canonical worker_execution_provenance@1, exact single compiled-boundary/single-worker identity posture, explicit provider-model-adapter fields distinct from attestation-provider identity, explicit runner-result/runner-provenance and optional verifier/attestation support refs, explicit attestation hash anchors, support-only emitted_artifact_refs, and fail-closed handling for raw-input bypass, prompt-authority drift, stale compiled-boundary reuse, runner-provenance hash mismatch, and incomplete support carriers."}
```

## V48C Worker Execution Envelope Evidence

```json
{"schema":"v48c_worker_execution_envelope_evidence@1","evidence_input_path":"artifacts/agent_harness/v114/evidence_inputs/v48c_worker_execution_envelope_evidence_v114.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS114.md#v114-continuation-contract-machine-checkable","merged_pr":"#336","merge_commit":"cf43eea67a928d7b3ad22614c388de652010301e","implementation_packages":["adeu_agent_harness"],"worker_envelope_implementation_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/worker_execution_envelope.py","worker_envelope_export_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py","task_run_boundary_instance_authoritative_schema_path":"packages/adeu_agent_harness/schema/task_run_boundary_instance.v1.json","task_run_boundary_instance_mirror_schema_path":"spec/task_run_boundary_instance.schema.json","worker_execution_attestation_authoritative_schema_path":"packages/adeu_agent_harness/schema/worker_execution_attestation.v1.json","worker_execution_attestation_mirror_schema_path":"spec/worker_execution_attestation.schema.json","worker_execution_provenance_authoritative_schema_path":"packages/adeu_agent_harness/schema/worker_execution_provenance.v1.json","worker_execution_provenance_mirror_schema_path":"spec/worker_execution_provenance.schema.json","test_reference_paths":["packages/adeu_agent_harness/tests/test_taskpack_binding.py","packages/adeu_agent_harness/tests/test_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_worker_execution_envelope.py","packages/adeu_agent_harness/tests/test_worker_execution_envelope_export_schema.py","packages/adeu_agent_harness/tests/test_taskpack_compile.py"],"accepted_boundary_instance_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48c/reference_task_run_boundary_instance.json","accepted_attestation_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48c/reference_worker_execution_attestation.json","accepted_provenance_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48c/reference_worker_execution_provenance.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v114/evidence_inputs/metric_key_continuity_assertion_v114.json","runtime_observability_comparison_path":"artifacts/agent_harness/v114/evidence_inputs/runtime_observability_comparison_v114.json","runtime_event_stream_path":"artifacts/agent_harness/v114/runtime/evidence/local/urm_events.ndjson","notes":"v114 evidence pins the released V48-C worker-envelope lane on main: one canonical task_run_boundary_instance@1, one canonical worker_execution_attestation@1, one canonical worker_execution_provenance@1, exact single compiled-boundary/single repo/single task/single worker posture, explicit provider/model/adapter identity distinct from attestation-provider identity, explicit runner-result/runner-provenance binding plus optional verifier/attestation support refs, explicit attestation hash anchors, support-only emitted_artifact_refs, and fail-closed handling for raw V48-A bypass, prompt-authority drift, runner-provenance hash mismatch, stale boundary reuse, and incomplete support carriers."}
```

## Recommendation (Post v114)

- gate decision:
  - `V48C_WORKER_EXECUTION_ENVELOPE_COMPLETE_ON_MAIN`
  - `V48_POLICY_TO_TASKPACK_AND_WORKER_ENFORCEMENT_BRANCH_ACTIVE_ON_MAIN`
- rationale:
  - `v114` closes the bounded `V48-C` worker-envelope seam on `main` by taking the
    released `V48-B` compiled binding as the only admitted source and deterministically
    binding one task/run boundary instance, one worker execution attestation, and one
    worker execution provenance chain over explicit released runner/verifier/attestation
    support carriers.
  - the shipped slice is attestation-first and still pre-conformance: it does not
    reopen descriptive semantics, ANM semantics, `V48-A` binding semantics, `V48-B`
    compiler semantics, generic runner/verifier/attestation kernel semantics,
    replayable post-run conformance, or multi-worker topology.
  - worker provider/model identity now remains explicit envelope-owned fact instead of
    being inferred from attestation-provider identity or ambient runtime convention.
  - attestation and provenance now remain hash-coherent with the released compiled
    boundary and with the released support artifacts they consume.
  - raw `V48-A` / `V45` / `V47` bypass, prompt-authority drift, stale boundary reuse,
    runner-provenance drift, and incomplete support carriers fail closed rather than
    being repaired by local convention.
  - authoritative schemas, mirrored exports, committed fixtures, and targeted tests
    remain in parity for all three released `V48-C` surfaces.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`-14 ms` vs `v113` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now records `V48-C` as closed on `main` and
    advances the branch-local default next path to `V48-D` / `vNext+115`.
