# Draft Stop-Gate Decision (Post vNext+80)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md`

Status: draft decision note (post-hoc closeout capture, March 25, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS80.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v80_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+80` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md`.
- This note captures `V40-D` architecture lowering closeout evidence only; it does not
  authorize UX lowering, API/web workbench surfaces, broader target-family release,
  direct repo mutation, or prompt-to-code generation by itself.
- Canonical `V40-D` release in v80 is carried by the extended
  `packages/adeu_architecture_compiler` projection surface, canonical
  `adeu_architecture_projection_bundle@1` and
  `adeu_architecture_projection_manifest@1`, authoritative and mirrored schema exports
  under `packages/adeu_architecture_compiler/schema/` and `spec/`, committed v80 ready
  and blocked fixture ladders, and canonical
  `v40d_architecture_core_ir_lowering_evidence@1`.
- The released v80 lane remains intentionally bounded:
  released `V40-A`, `V40-B`, and `V40-C` artifacts remain authoritative inputs,
  lowering is legal only into `adeu_core_ir@0.1`, blocked units carry empty
  `output_artifact_refs`, ready units require ready conformance plus no active
  checkpoint-trace blockers, and UX or broader target-family widening remains deferred.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `9ae9972fa937cd5167c207390392878fb1b89bde`
- arc-completion CI runs:
  - PR `#302`
    - head commit: `6b4d68b90c945891cf263ae344485be36d3719ba`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23518824543`
    - conclusion: `success`
  - branch push before merge
    - head commit: `6b4d68b90c945891cf263ae344485be36d3719ba`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23518823593`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `9ae9972fa937cd5167c207390392878fb1b89bde`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23524300090`
    - conclusion: `success`
- merged implementation PRs:
  - `#302` (`Implement V40-D core IR lowering lane`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v80_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v80_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v80_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v80/evidence_inputs/metric_key_continuity_assertion_v80.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v80/evidence_inputs/runtime_observability_comparison_v80.json`
  - `V40-D` architecture lowering evidence input:
    `artifacts/agent_harness/v80/evidence_inputs/v40d_architecture_core_ir_lowering_evidence_v80.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v80/runtime/evidence/codex/copilot/v80-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v80/runtime/evidence/codex/copilot/v80-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v80 remains carried by the typed
    lowering schema/fixture/evidence artifacts plus the closeout quality and
    stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS80_EDGES.md`

## Exit-Criteria Check (vNext+80)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V40-D` merged with green CI | required | `pass` | PR `#302`, merge commit `9ae9972fa937cd5167c207390392878fb1b89bde`, Actions runs `23518824543`, `23518823593`, and `23524300090` |
| Canonical projection artifact families validate and export cleanly | required | `pass` | authoritative/mirrored schemas under `packages/adeu_architecture_compiler/schema/` and `spec`, `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`, and `v40d_architecture_core_ir_lowering_evidence_v80.json` |
| Released `V40-A` root, `V40-B` conformance, and `V40-C` checkpoint surfaces remain explicit consumed inputs | required | `pass` | committed v80 semantic/conformance/checkpoint derivatives, `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/projection.py`, and `upstream_root_lineage_verified = true`, `upstream_conformance_lineage_verified = true`, `upstream_checkpoint_lineage_verified = true` |
| Lowering remains lawful only to `adeu_core_ir@0.1` | required | `pass` | committed ready/blocked projection fixtures, `projection.py`, and `target_family_only_verified = true` |
| Ready units emit authoritative `adeu_core_ir@0.1` only with exact output lineage binding | required | `pass` | committed ready bundle/manifest/core-ir fixtures, `projection.py`, and `ready_output_lineage_binding_verified = true` |
| Blocked units remain honest and non-emitting | required | `pass` | blocked fixture ladder, `projection.py`, and `blocked_output_honesty_verified = true` |
| Per-unit readiness remains downstream of released conformance and checkpoint lineage | required | `pass` | `projection.py`, committed mixed ready/blocked fixture coverage, and `ready_requires_ready_conformance_and_no_active_blockers_verified = true` |
| Manifest and bundle remain mutually consistent | required | `pass` | `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40d.py` and `manifest_bundle_consistency_verified = true` |
| Review-driven hardening for output-lineage binding and manifest blocker consistency is preserved | required | `pass` | merged follow-up commit `6b4d68b90c945891cf263ae344485be36d3719ba`, `test_v40d_ready_bundle_rejects_output_lineage_drift`, `test_v40d_manifest_rejects_blocked_ready_without_active_trace_lineage`, and `review_hardening_preserved = true` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v80_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v80/evidence_inputs/metric_key_continuity_assertion_v80.json` records exact keyset equality versus v79 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v80/evidence_inputs/runtime_observability_comparison_v80.json` |

## Stop-Gate Summary

```json
{
  "schema": "v80_closeout_stop_gate_summary@1",
  "arc": "vNext+80",
  "target_path": "V40-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v79": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": 6
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v79_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v80_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+79","baseline_elapsed_ms":84,"baseline_source":"artifacts/stop_gate/report_v79_closeout.md","current_arc":"vNext+80","current_elapsed_ms":90,"current_source":"artifacts/stop_gate/report_v80_closeout.md","delta_ms":6,"notes":"v80 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V40-D adeu_core_ir lowering lane with canonical projection bundle/manifest lineage and blocked-vs-ready output honesty.","schema":"runtime_observability_comparison@1"}
```

## V40D Architecture Lowering Evidence

```json
{"blocked_bundle_fixture_hash":"579cd12032313d1bc0b2890cf52e5e5480b037ad05c6f30b0cf66e42c2cccc37","blocked_bundle_fixture_path":"apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_blocked_reference.json","blocked_manifest_fixture_hash":"0e10f377b4a6a642654ab948b69151861c0f9da03551c2471655a6a8342cefee","blocked_manifest_fixture_path":"apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_blocked_reference.json","blocked_output_honesty_verified":true,"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md#v80-continuation-contract-machine-checkable","core_ir_fixture_hash":"df882365ef5a59dca55e80919201e07733ab27d540376a0c968591e372a6f556","core_ir_fixture_path":"apps/api/fixtures/architecture/vnext_plus80/adeu_core_ir_v80_ready_reference.json","evidence_input_path":"artifacts/agent_harness/v80/evidence_inputs/v40d_architecture_core_ir_lowering_evidence_v80.json","export_test_reference_hash":"1d8127215f82b0fa9a1323e1b1be5704ea147d8c22959cbf8f08d996dc5d96ff","export_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py","implementation_source_hash":"0d2e114657459b51a5ef4263cac683d834a58ace49f85f90a5b2fb142aa6f7ca","implementation_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/projection.py","manifest_bundle_consistency_verified":true,"merge_commit":"9ae9972fa937cd5167c207390392878fb1b89bde","merged_pr":"#302","model_test_reference_hash":"6c6712daefe87033601daf3d837717ddac6bb68fda26713c790c331e12572ca4","model_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40d.py","notes":"v80 evidence pins the released V40-D lowering lane on main: canonical projection bundle and manifest schema exports, authoritative adeu_core_ir@0.1 ready lowering, blocked-honesty fixture coverage, exact upstream semantic/conformance/checkpoint lineage, and the merged review-driven hardening for emitted core-ir metadata binding and manifest blocker/readiness consistency.","package_surface_hash":"a64404286db79993d4de7731023f090ffa279694b044c794724da3f1b55261e6","package_surface_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py","policy_sources":[{"path":"AGENTS.md","sha256":"4ee9bbb70d02036e72deaaba7348a3b7e8d93b0a7431535a4597be08b7af7f93"},{"path":"docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md","sha256":"73c22a4560969d6d93563a024539b0c7a61f310ad2064cbbf479a058edc86527"},{"path":"docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md","sha256":"228f1ac907cbea5afeac925df9fe567f919ed411891a0178c0fbd679aadbec0c"},{"path":"docs/LOCKED_CONTINUATION_vNEXT_PLUS79.md","sha256":"21004d598dddccd3538f353fe021625430b5664cd261ef27ba98e72729f78ee9"},{"path":"docs/LOCKED_CONTINUATION_vNEXT_PLUS80.md","sha256":"603410185d1a9b570bf383091a2e31719c9220dc8f9d5ef6942a9dc7cafd24bd"}],"ready_bundle_fixture_hash":"32d98a0bcb2bca510a7e62c0c876d5dfa0424ecbd8afd5c530b0ea86671d4892","ready_bundle_fixture_path":"apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_bundle_v80_ready_reference.json","ready_manifest_fixture_hash":"91d5598edb3d8952e6d7202c68cca39add997565a8c65138833994c392bd2067","ready_manifest_fixture_path":"apps/api/fixtures/architecture/vnext_plus80/adeu_architecture_projection_manifest_v80_ready_reference.json","ready_output_lineage_binding_verified":true,"ready_requires_ready_conformance_and_no_active_blockers_verified":true,"review_hardening_preserved":true,"schema":"v40d_architecture_core_ir_lowering_evidence@1","schema_export_parity_verified":true,"schema_export_source_hash":"e87f086502de41b62484c29c3f6c7eb94f8f91e287920a37a78dd9400db8e922","schema_export_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py","schema_reference_hashes":{"projection_bundle":{"authoritative_hash":"b1d86e3720aba97422cf2c0f67c67944ed6a86ab160726bd582f911ab245b726","authoritative_path":"packages/adeu_architecture_compiler/schema/adeu_architecture_projection_bundle.v1.json","mirror_hash":"b1d86e3720aba97422cf2c0f67c67944ed6a86ab160726bd582f911ab245b726","mirror_matches_authoritative":true,"mirror_path":"spec/adeu_architecture_projection_bundle.schema.json"},"projection_manifest":{"authoritative_hash":"d5f1b26457a116a8365b652ab4c0ad62ea75c9f98f67b7f483cff5fd5215716d","authoritative_path":"packages/adeu_architecture_compiler/schema/adeu_architecture_projection_manifest.v1.json","mirror_hash":"d5f1b26457a116a8365b652ab4c0ad62ea75c9f98f67b7f483cff5fd5215716d","mirror_matches_authoritative":true,"mirror_path":"spec/adeu_architecture_projection_manifest.schema.json"}},"target_family_only_verified":true,"upstream_checkpoint_lineage_verified":true,"upstream_conformance_lineage_verified":true,"upstream_root_lineage_verified":true}
```

## Recommendation (Post v80)

- gate decision:
  - `V40D_ARCHITECTURE_CORE_IR_LOWERING_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v80 closes the bounded `V40-D` baseline with canonical projection bundle and
    projection manifest artifact families, authoritative and mirrored schema exports,
    committed ready and blocked fixture ladders, authoritative
    `adeu_core_ir@0.1` ready lowering, and canonical
    `v40d_architecture_core_ir_lowering_evidence@1` integrated on `main`.
  - the released lane remains explicitly bounded to one honest downstream lowering:
    released semantic-root, conformance, and checkpoint-trace artifacts remain
    authoritative consumed inputs; blocked units remain non-emitting; and no UX,
    application-family, or broader target-family lowering shipped in v80.
  - review-driven hardening on the merged PR now preserves exact emitted core-ir
    lineage binding for ready units and manifest/bundle blocker-readiness consistency.
  - no stop-gate schema-family, metric-key, or runtime-observability regressions were
    introduced by the lane, and the current planned `V40-D` lowering baseline is now
    complete on `main` at its intentionally bounded scope.
