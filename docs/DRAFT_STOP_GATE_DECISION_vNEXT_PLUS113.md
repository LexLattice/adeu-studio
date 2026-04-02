# Draft Stop-Gate Decision (Post vNext+113)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS113.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v113_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+113` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md`.
- This note captures bounded `V48-B` compiler evidence only; it does not authorize
  worker attestation release, worker provenance release, post-run conformance release,
  signature-envelope release, execution-result release, multi-worker topology,
  repo-wide taskpack generation, execution posture expansion, approval posture, waiver
  issuance, or deferral issuance by itself.
- Canonical `V48-B` release in `v113` is carried by the shipped
  `adeu_agent_harness` source, schema-export, deterministic fixtures, and targeted
  test surfaces plus the canonical `v48b_policy_to_taskpack_compiler_evidence@1`
  evidence input under `artifacts/agent_harness/v113/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#335` (`V48-B: add compiled taskpack binding bridge`)
- arc-completion merge commit: `e399103f5e751e57678c4d31b7397714c84c922e`
- merged-at timestamp: `2026-04-02T20:56:28Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v113_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v113_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v113_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v113/evidence_inputs/metric_key_continuity_assertion_v113.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v113/evidence_inputs/runtime_observability_comparison_v113.json`
  - `V48-B` release evidence input:
    `artifacts/agent_harness/v113/evidence_inputs/v48b_policy_to_taskpack_compiler_evidence_v113.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v113/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS113_EDGES.md`

## Exit-Criteria Check (vNext+113)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V48-B` merged with green CI | required | `pass` | PR `#335`, merge commit `e399103f5e751e57678c4d31b7397714c84c922e`, checks `python/web/lean-formal = pass` |
| Released compiled binding surface ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_agent_harness/schema/compiled_policy_taskpack_binding.v1.json`, `spec/compiled_policy_taskpack_binding.schema.json`, and parity coverage in `packages/adeu_agent_harness/tests/test_compiled_taskpack_binding_export_schema.py` |
| Accepted compiled fixture replays deterministically on repeated compile runs | required | `pass` | committed reference fixture `packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_policy_taskpack_binding.json` and test `test_v48b_reference_compiled_binding_replays_deterministically` |
| Every accepted compile request binds exactly one released `V48-A` profile, one compiler selection, and one declared task identity | required | `pass` | cardinality validation in `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`, committed spec fixture `packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_taskpack_binding_spec.json`, and test `test_v48b_rejects_multiple_binding_profile_refs` |
| The `V48-A` binding profile lowers through exactly one released pipeline profile plus one released registry before reusing `compile_taskpack(...)` unchanged | required | `pass` | bridge logic in `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`, committed fixtures `packages/adeu_agent_harness/tests/fixtures/v48b/reference_pipeline_profile.json` and `packages/adeu_agent_harness/tests/fixtures/v48b/reference_profile_registry.json`, and tests `test_v48b_reference_compiled_binding_replays_deterministically` plus `test_v48b_rejects_malformed_pipeline_profile_bridge` |
| Released compiler authority inputs remain explicit through `source_semantic_arc`, evidence-manifest / surface-diff resolution, and `compiled_commitments_ir_path` | required | `pass` | authority-input resolution in `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`, committed reference fixture, and test `test_v48b_rejects_ambiguous_source_semantic_arc` |
| Compiled boundary identity remains explicit and carries one worker subject kind plus one worker subject ref | required | `pass` | `compiled_boundary_identity_hash`, `worker_subject_kind`, and `worker_subject_ref` in the released schema pair, committed reference fixture, and deterministic replay coverage in `test_v48b_reference_compiled_binding_replays_deterministically` |
| Emitted component set stays bounded to released kernel carriers with sibling `taskpack_manifest.json` and replayable bundle hash | required | `pass` | emitted component refs in `packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_policy_taskpack_binding.json`, compiler implementation in `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`, and replay coverage in `test_v48b_reference_compiled_binding_replays_deterministically` |
| `TASKPACK.md` preserves released section order, attribution markers, and section-termination posture | required | `pass` | delegation to the unchanged released compiler in `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py`, committed replay fixture set, and deterministic taskpack-compile coverage in `packages/adeu_agent_harness/tests/test_taskpack_compile.py` |
| Raw-input bypass, binding-profile hash drift, malformed bridge inputs, and unsupported compiled output drift fail closed | required | `pass` | reject fixtures under `packages/adeu_agent_harness/tests/fixtures/v48b/` and tests `test_v48b_rejects_raw_v47_bypass`, `test_v48b_rejects_binding_profile_hash_mismatch`, and `test_v48b_rejects_malformed_pipeline_profile_bridge` |
| Out-dir and semantic-authority path escapes fail closed instead of escaping the repo root | required | `pass` | path-containment checks in `packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py` and tests `test_v48b_rejects_out_dir_symlink_escape` plus `test_v48b_rejects_semantic_authority_symlink_escape` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v113_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v113/evidence_inputs/metric_key_continuity_assertion_v113.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v113/evidence_inputs/runtime_observability_comparison_v113.json` |

## Stop-Gate Summary

```json
{
  "schema": "v113_closeout_stop_gate_summary@1",
  "arc": "vNext+113",
  "target_path": "V48-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v112": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 125,
  "runtime_observability_delta_ms": 31
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v112_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v113_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+112","current_arc":"vNext+113","baseline_source":"artifacts/stop_gate/report_v112_closeout.md","current_source":"artifacts/stop_gate/report_v113_closeout.md","baseline_elapsed_ms":94,"current_elapsed_ms":125,"delta_ms":31,"notes":"v113 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V48-B compiler lane: one canonical compiled_policy_taskpack_binding@1, explicit lowering from one released V48-A binding profile into exactly one released taskpack/pipeline_profile@1 plus one taskpack_profile_registry@1, unchanged reuse of compile_taskpack(...), explicit source_semantic_arc and semantic-compiler authority-input resolution, deterministic emitted TASKPACK/ACCEPTANCE/ALLOWLIST/FORBIDDEN/COMMANDS/EVIDENCE_SLOTS carriers plus sibling taskpack_manifest.json, explicit bundle hash, and fail-closed raw-input bypass, hash-drift, malformed-bridge, and repo-escape handling."}
```

## V48B Policy-To-Taskpack Compiler Evidence

```json
{"schema":"v48b_policy_to_taskpack_compiler_evidence@1","evidence_input_path":"artifacts/agent_harness/v113/evidence_inputs/v48b_policy_to_taskpack_compiler_evidence_v113.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS113.md#v113-continuation-contract-machine-checkable","merged_pr":"#335","merge_commit":"e399103f5e751e57678c4d31b7397714c84c922e","implementation_packages":["adeu_agent_harness"],"compiled_binding_implementation_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/compiled_taskpack_binding.py","compiled_binding_export_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py","compiled_binding_authoritative_schema_path":"packages/adeu_agent_harness/schema/compiled_policy_taskpack_binding.v1.json","compiled_binding_mirror_schema_path":"spec/compiled_policy_taskpack_binding.schema.json","test_reference_paths":["packages/adeu_agent_harness/tests/test_compiled_taskpack_binding.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_taskpack_compile.py"],"accepted_compiled_binding_spec_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_taskpack_binding_spec.json","accepted_compiled_binding_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_policy_taskpack_binding.json","accepted_pipeline_profile_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reference_pipeline_profile.json","accepted_profile_registry_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reference_profile_registry.json","rejected_multiple_binding_profile_refs_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reject_multiple_binding_profile_refs_spec.json","rejected_raw_v47_bypass_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reject_raw_v47_bypass_spec.json","rejected_binding_profile_hash_mismatch_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reject_binding_profile_hash_mismatch_spec.json","rejected_source_semantic_arc_ambiguous_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reject_source_semantic_arc_ambiguous_spec.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v113/evidence_inputs/metric_key_continuity_assertion_v113.json","runtime_observability_comparison_path":"artifacts/agent_harness/v113/evidence_inputs/runtime_observability_comparison_v113.json","runtime_event_stream_path":"artifacts/agent_harness/v113/runtime/evidence/local/urm_events.ndjson","notes":"v113 evidence pins the released V48-B compiler lane on main: one canonical compiled_policy_taskpack_binding@1, exact single-profile/single-compiler/single-task identity compile posture, explicit lowering from the released V48-A binding profile into one released pipeline profile and one released profile registry, unchanged compile_taskpack(...) reuse, explicit source_semantic_arc and semantic-compiler authority-input resolution, deterministic taskpack component and sibling manifest emission, explicit compiled-boundary identity plus bundle hash, and fail-closed handling for raw-input bypass, binding-profile hash drift, malformed bridge inputs, out-dir symlink escape, and semantic-authority path escape."}
```

## Recommendation (Post v113)

- gate decision:
  - `V48B_POLICY_TO_TASKPACK_COMPILER_COMPLETE_ON_MAIN`
  - `V48_POLICY_TO_TASKPACK_AND_WORKER_ENFORCEMENT_BRANCH_ACTIVE_ON_MAIN`
- rationale:
  - v113 closes the bounded `V48-B` policy-to-taskpack compiler seam on `main` by
    taking the released `V48-A` binding profile as the only admitted bridge input and
    deterministically lowering it into released taskpack carriers without reopening
    generic kernel semantics.
  - the shipped slice is compiler-first and still non-attestational: it does not
    reopen descriptive semantics, ANM semantics, `V48-A` binding semantics, worker-run
    attestation, worker provenance, post-run conformance, or multi-worker topology.
  - the bridge to the released kernel is now explicit rather than ambient:
    exactly one `taskpack/pipeline_profile@1` plus one
    `taskpack_profile_registry@1` are materialized and then delegated to the unchanged
    released `compile_taskpack(...)` entrypoint.
  - compiler authority inputs are now explicit through one `source_semantic_arc`,
    semantic-compiler evidence-manifest / surface-diff resolution, and one carried
    `compiled_commitments_ir_path`.
  - emitted taskpack carriers remain bounded to the released kernel component set and
    one sibling `taskpack_manifest.json`, with explicit manifest/component hash
    consistency and replayable `bundle_hash`.
  - raw `V45` / `V47` bypass, stale binding-profile reuse, malformed bridge inputs,
    and repo-escape path manipulation now fail closed rather than being repaired by
    local convention.
  - authoritative schema, mirrored export, committed fixtures, and targeted tests stay
    in parity for the released compiled-binding surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+31 ms` vs v112 baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now records `V48-B` as closed on `main` and
    advances the branch-local default next path to `V48-C` / `vNext+114`.
