# Draft Stop-Gate Decision (Post vNext+78)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md`

Status: draft decision note (post-hoc closeout capture, March 24, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS78.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v78_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+78` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md`.
- This note captures `V40-B` architecture deterministic assembly, conformance, and
  gating closeout evidence only; it does not authorize checkpoint/oracle execution,
  checkpoint traces, projection bundles, projection manifests, `adeu_core_ir`
  lowerings, UX lowerings, API/workbench release, or direct prompt-to-code generation
  by itself.
- Canonical `V40-B` release in v78 is carried by the activated
  `packages/adeu_architecture_compiler` surface, canonical
  `adeu_architecture_conformance_report@1`, authoritative and mirrored schema exports
  under `packages/adeu_architecture_compiler/schema/` and `spec/`, committed v78
  ready/blocked fixture ladders, and canonical
  `v40b_architecture_compiler_evidence@1`.
- The released v78 lane remains intentionally bounded:
  `packages/adeu_architecture_ir` remains authoritative for consumed root semantics,
  `packages/adeu_architecture_compiler` is the only newly activated package, consumed
  root lineage remains explicit, `ASIR-H-xxx` remains deferred, `human_escalation_refs`
  remains static deterministic escalation lineage only, and downstream hybrid and
  lowering surfaces remain deferred.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `b4f3dcb98e8a063ef9a26df7833945570b600044`
- arc-completion CI runs:
  - PR `#300`
    - head commit: `f253ee3a57eb8693bed5bb12c1fd61a93143e7eb`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23466926561`
    - conclusion: `success`
  - branch push before merge
    - head commit: `f253ee3a57eb8693bed5bb12c1fd61a93143e7eb`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23466924160`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `b4f3dcb98e8a063ef9a26df7833945570b600044`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23467401856`
    - conclusion: `success`
- merged implementation PRs:
  - `#300` (`Implement v78 architecture compiler baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v78_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v78_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v78_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v78/evidence_inputs/metric_key_continuity_assertion_v78.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v78/evidence_inputs/runtime_observability_comparison_v78.json`
  - V40-B architecture compiler evidence input:
    `artifacts/agent_harness/v78/evidence_inputs/v40b_architecture_compiler_evidence_v78.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v78/runtime/evidence/codex/copilot/v78-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v78/runtime/evidence/codex/copilot/v78-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v78 remains carried by the typed
    conformance schema/fixture/evidence artifacts plus the closeout quality and
    stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS78_EDGES.md`

## Exit-Criteria Check (vNext+78)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V40-B` merged with green CI | required | `pass` | PR `#300`, merge commit `b4f3dcb98e8a063ef9a26df7833945570b600044`, Actions runs `23466926561`, `23466924160`, and `23467401856` |
| `packages/adeu_architecture_compiler` is the only newly activated package in this slice | required | `pass` | merged package surface, `Makefile`, and unchanged `V40-A` root-family package ownership |
| Canonical `adeu_architecture_conformance_report@1` validates and exports cleanly | required | `pass` | `packages/adeu_architecture_compiler/schema/adeu_architecture_conformance_report.v1.json`, `spec/adeu_architecture_conformance_report.schema.json`, and `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py` |
| Deterministic conformance replay preserves exact consumed-root lineage | required | `pass` | committed v78 fixtures, `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40b.py`, and `v40b_architecture_compiler_evidence_v78.json` |
| Stable deterministic `ASIR-O`, `ASIR-E`, `ASIR-D`, `ASIR-U`, and `ASIR-P` check families are emitted with fixed required coverage | required | `pass` | `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/conformance.py`, committed v78 fixtures, and `v40b_architecture_compiler_evidence_v78.json` |
| Whole-ASIR integrity and section-local validation fail closed on required violations | required | `pass` | `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40b.py` including gate-coverage and imported-report tamper checks |
| `projection_readiness` remains explicit, deterministic, and honest | required | `pass` | committed blocked/ready conformance fixtures and `v40b_architecture_compiler_evidence_v78.json` |
| `human_escalation_refs` remains static deterministic escalation lineage only | required | `pass` | merged follow-up commit `f253ee3a57eb8693bed5bb12c1fd61a93143e7eb`, updated v78 blocked fixture, and `test_v40b_compiler_blocks_on_static_human_escalation_rule` |
| `emitted_artifact_refs` remains structurally present but empty | required | `pass` | committed v78 fixtures, schema export, and `test_v40b_compiler_rejects_nonempty_emitted_artifact_refs` |
| Review-driven config-hash and required-check-profile hardening remain preserved | required | `pass` | merged follow-up commit `f253ee3a57eb8693bed5bb12c1fd61a93143e7eb`, updated fixtures, and `v40b_architecture_compiler_evidence_v78.json` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v78_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v78/evidence_inputs/metric_key_continuity_assertion_v78.json` records exact keyset equality versus v77 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v78/evidence_inputs/runtime_observability_comparison_v78.json` |

## Stop-Gate Summary

```json
{
  "schema": "v78_closeout_stop_gate_summary@1",
  "arc": "vNext+78",
  "target_path": "V40-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v77": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 85,
  "runtime_observability_delta_ms": -6
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v77_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v78_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+77","baseline_elapsed_ms":91,"baseline_source":"artifacts/stop_gate/report_v77_closeout.md","current_arc":"vNext+78","current_elapsed_ms":85,"current_source":"artifacts/stop_gate/report_v78_closeout.md","delta_ms":-6,"notes":"v78 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V40-B deterministic compiler, canonical conformance report, consumed-root lineage, and blocked-vs-ready gating baseline.","schema":"runtime_observability_comparison@1"}
```

## V40B Architecture Compiler Evidence

```json
{"advisory_check_non_blocking_verified":true,"blocked_fixture_hash":"a5044db1f747aa39367d364bc67f436e7cc3e2f323f7554a8c57bf99b88386f4","blocked_fixture_path":"apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json","blocked_ready_fixture_replay_verified":true,"check_family_split_verified":true,"compiler_config_hash_locked_to_profile":true,"conformance_schema_reference_hash":"e61148aaf49d14aa9d1f0ec54ec6e663542c95d15f0c09d08787ea1afaf5fb0f","conformance_schema_reference_mirror_hash":"e61148aaf49d14aa9d1f0ec54ec6e663542c95d15f0c09d08787ea1afaf5fb0f","conformance_schema_reference_mirror_path":"spec/adeu_architecture_conformance_report.schema.json","conformance_schema_reference_path":"packages/adeu_architecture_compiler/schema/adeu_architecture_conformance_report.v1.json","consumed_root_lineage_verified":true,"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md#v78-continuation-contract-machine-checkable","emitted_artifact_refs_empty_verified":true,"evidence_input_path":"artifacts/agent_harness/v78/evidence_inputs/v40b_architecture_compiler_evidence_v78.json","export_test_reference_hash":"7508144bb4de2e2409c485fce1255161ff95a81c770971ef18feaf991e8d6315","export_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py","implementation_source_hash":"cc87b220686052069de4bbe8472e94cbad47ba82ced2c85cdfb1d2fc6cdb22d3","implementation_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/conformance.py","merged_pr":"#300","model_test_reference_hash":"f1d98e5bf6f195bf05d79b75903e0f94f411bc6bcf17c5cb8af63efedbc701d8","model_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40b.py","notes":"v78 evidence pins the released V40-B deterministic compiler surface: canonical adeu_architecture_conformance_report@1 schema exports, consumed-root lineage, whole-ASIR plus section-local fail-closed validation, required-check profile coverage, static human-escalation lineage, blocked-vs-ready gating honesty, and the review-driven hardening for config-hash replay and imported-report tamper resistance on main.","policy_sources":[{"path":"AGENTS.md","sha256":"411d5c18cf5645d60f9873d1d3f81bbff0e61b2770bbead4c1a9509b64058f67"},{"path":"docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md","sha256":"2e280eb0eab58a11619e37a92a374558dba2e23c6839eb5c0f5b0ad8984313ba"},{"path":"docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md","sha256":"4f01d8b09acbe1d68013412c97528fa89cbfca980353c812ae0308c8836b53ef"}],"pre_projection_scope_boundary_preserved":true,"ready_fixture_hash":"2282cc24be4eb87a7c82c58d6f515b7db568ddbc88f0f55af5141d1adbe62c01","ready_fixture_path":"apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json","ready_semantic_ir_derivative_hash":"5b705cfdd43339ea341580df84f41b43fc11da3482ef61448e2d3438da61af54","ready_semantic_ir_derivative_path":"apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_semantic_ir_v78_ready_derivative.json","required_check_fail_closed_verified":true,"required_check_profile_coverage_verified":true,"schema":"v40b_architecture_compiler_evidence@1","schema_export_parity_verified":true,"schema_export_source_hash":"756dd74ddac2c86bbefeb2b1169133d6fcb7eb6d9cdc2d8a77c8df7b604607ee","schema_export_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py","static_human_escalation_lineage_verified":true,"v40a_root_consumption_without_drift_verified":true}
```

## Recommendation (Post v78)

- gate decision:
  - `V40B_ARCHITECTURE_COMPILER_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v78 closes the bounded `V40-B` baseline with activated
    `packages/adeu_architecture_compiler`, canonical
    `adeu_architecture_conformance_report@1`, authoritative/mirrored schema exports,
    committed blocked/ready reference fixtures, and canonical
    `v40b_architecture_compiler_evidence@1` integrated on `main`.
  - the released lane remains explicitly bounded to deterministic conformance only:
    no checkpoint/oracle execution, no checkpoint trace artifact family, no projection
    bundle or manifest, no `adeu_core_ir` lowering, and no UX/API widening shipped in
    v78.
  - review-driven hardening on the merged PR now preserves config-hash replay
    integrity, exact required-check profile coverage, static deterministic
    human-escalation lineage, and imported-report fail-closed posture within the
    released conformance surface.
  - no stop-gate schema-family, metric-key, or runtime-observability regressions were
    introduced by the lane, and the current planned `V40-B` deterministic compiler
    baseline is now complete on `main` at its intentionally bounded scope.
