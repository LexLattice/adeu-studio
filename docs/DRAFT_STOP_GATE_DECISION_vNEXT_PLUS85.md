# Draft Stop-Gate Decision (Post vNext+85)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md`

Status: draft decision note (post-hoc closeout capture, March 26, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS85.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v85_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+85` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md`.
- This note captures `V41-C` practical observed-implementation closeout evidence
  only; it does not authorize repo-grounded intended
  `adeu_architecture_semantic_ir@1` compile,
  `adeu_architecture_alignment_report@1`, CLI runner release, API/web inspection
  routes, remediation/repo-mutation planning, or any intended/alignment authority
  inside the observation lane.
- Canonical `V41-C` release in v85 is carried by the extended
  `packages/adeu_architecture_compiler` observation surface, the released
  `adeu_architecture_observation_frame@1` schema under
  `packages/adeu_architecture_compiler/schema/` and `spec/`, the committed
  observation reference fixture under
  `apps/api/fixtures/architecture/vnext_plus85/`, and the canonical
  `v41c_architecture_observation_frame_evidence@1` evidence input under
  `artifacts/agent_harness/v85/evidence_inputs/`.
- The released v85 lane remains intentionally bounded: exact consumption of the
  released `V41-A` request boundary plus `V41-B` settlement carry-through,
  facts-only observed extraction, explicit direct-vs-derived marking, grounded
  provenance closure, explicit unresolved observations, and upstream blocked
  settlement posture remain authoritative; intended compile, alignment, runner
  release, and remediation remain deferred.
- Supporting downstream fixture refreshes in the merged PR remain replay-preserving
  maintenance only; they do not widen the released `V41-C` semantic scope.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `ad78e900b60b48f8c238df474f460e53e7685eec`
- arc-completion CI runs:
  - PR `#307`
    - head commit: `7be5e6a6afee8e59097564a1eca59dabf6405f51`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23572115404`
    - conclusion: `success`
  - branch push before merge
    - head commit: `7be5e6a6afee8e59097564a1eca59dabf6405f51`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23572113948`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `ad78e900b60b48f8c238df474f460e53e7685eec`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23572324663`
    - conclusion: `success`
- merged implementation PRs:
  - `#307` (`Implement v85 observation frame`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v85_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v85_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v85_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v85/evidence_inputs/metric_key_continuity_assertion_v85.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v85/evidence_inputs/runtime_observability_comparison_v85.json`
  - `V41-C` observation evidence input:
    `artifacts/agent_harness/v85/evidence_inputs/v41c_architecture_observation_frame_evidence_v85.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v85/runtime/evidence/codex/copilot/v85-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v85/runtime/evidence/codex/copilot/v85-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v85 remains carried by the typed
    observation implementation, exact request/settlement consumption, facts-only
    extraction, direct-vs-derived marking, unresolved-observation preservation,
    schema parity, committed fixture replay, and the closeout quality and stop-gate
    bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS85_EDGES.md`

## Exit-Criteria Check (vNext+85)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V41-C` merged with green CI | required | `pass` | PR `#307`, merge commit `ad78e900b60b48f8c238df474f460e53e7685eec`, Actions runs `23572115404`, `23572113948`, and `23572324663` |
| Canonical `adeu_architecture_observation_frame@1` artifact ships with authoritative/mirrored schema parity | required | `pass` | `packages/adeu_architecture_compiler/schema/adeu_architecture_observation_frame.v1.json`, `spec/adeu_architecture_observation_frame.schema.json`, and `observation_schema_reference_mirror_matches_authoritative = true` |
| Observation consumes the released `V41-A` request boundary exactly | required | `pass` | `observation.py`, `test_v41c_observation_fixture_validates_and_replays`, `analysis_request_ref = apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_analysis_request_v85_observation_derivative.json`, and `source_set_hash = 0420b6ef8626fb4e5fdecec355952857554499d13fda12d798e4e5570b62278e` |
| Observation consumes the released `V41-B` settlement boundary exactly and preserves upstream blocked posture | required | `pass` | `settlement_frame_ref = apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_analysis_settlement_frame_v85_observation_derivative.json`, `upstream_compile_entitlement = blocked`, `upstream_blocking_ref_count = 2`, `test_v41c_rejects_upstream_compile_entitlement_drift`, and `test_v41c_rejects_upstream_blocking_ref_drift` |
| Facts-only observation and anti-collapse guards remain enforced | required | `pass` | `test_v41c_rejects_alignment_creep`, `facts_only_observation_verified = true`, and `downstream_intended_alignment_runner_deferred = true` |
| Direct-vs-derived marking, provenance closure, and cross-entry grounding remain explicit | required | `pass` | `direct_observation_count = 11`, `derived_observation_count = 2`, `provenance_closure_verified = true`, `cross_entry_grounding_verified = true`, and `test_v41c_rejects_workflow_ref_outside_typed_entries` |
| Missing implementation facts remain explicit unresolved observations instead of invented structure | required | `pass` | `unresolved_observation_count = 1`, `unresolved_reason_kinds = [\"requires_non_source_context\"]`, `unresolved_observation_preservation_verified = true`, and `test_v41c_rejects_unresolved_observation_without_reason_kind` |
| Observation semantics stay source-grounded rather than documentation- or filename-driven | required | `pass` | `test_v41c_rejects_documentation_as_observed_source_ref`, `documentation_as_fact_source_rejected = true`, and `test_v41c_uses_observable_kind_not_filename_substrings_for_resolution` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v85_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v85/evidence_inputs/metric_key_continuity_assertion_v85.json` records exact keyset equality versus v84 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v85/evidence_inputs/runtime_observability_comparison_v85.json` |

## Stop-Gate Summary

```json
{
  "schema": "v85_closeout_stop_gate_summary@1",
  "arc": "vNext+85",
  "target_path": "V41-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v84": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 97,
  "runtime_observability_delta_ms": -37
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v84_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v85_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+84","baseline_elapsed_ms":134,"baseline_source":"artifacts/stop_gate/report_v84_closeout.md","current_arc":"vNext+85","current_elapsed_ms":97,"current_source":"artifacts/stop_gate/report_v85_closeout.md","delta_ms":-37,"notes":"v85 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V41-C facts-only observation frame lane with exact request/settlement carry-through, direct-vs-derived marking, explicit unresolved observations, and no intended/alignment/remediation authority.","schema":"runtime_observability_comparison@1"}
```

## V41C Observation-Frame Evidence

```json
{"analysis_request_fixture_hash":"b09a69da849a4c8b080142f3558f22fba59e081dfc12feee2831d8df24d0e949","analysis_request_fixture_path":"apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_analysis_request_v85_observation_derivative.json","analysis_request_id":"v41a_v85_architecture_ir_observation_request_derivative","analysis_request_ref":"apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_analysis_request_v85_observation_derivative.json","blocked_settlement_carrythrough_verified":true,"canonical_replay_verified":true,"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md#v41c_practical_analysis_observation_contract@1","cross_entry_grounding_verified":true,"derived_observation_count":2,"direct_observation_count":11,"direct_vs_derived_marking_verified":true,"documentation_as_fact_source_rejected":true,"downstream_intended_alignment_runner_deferred":true,"evidence_input_path":"artifacts/agent_harness/v85/evidence_inputs/v41c_architecture_observation_frame_evidence_v85.json","export_test_reference_hash":"390e741afa86aa4349eecd75da32c3390506a523e0e525e69c85188cb0314851","export_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py","facts_only_observation_verified":true,"implementation_source_hash":"d4e154c56626c7a1fdd0727ef71fb28628490f2e3212ae139a2b3bce688ec825","implementation_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/observation.py","materialized_replay_verified":true,"merge_commit":"ad78e900b60b48f8c238df474f460e53e7685eec","merged_pr":"#307","metric_key_cardinality":80,"metric_key_exact_set_equal_v84":true,"model_test_reference_hash":"f00d8472357b37c4922d707020151eba9bf7abe888cfbc04322385325f27d400","model_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41c.py","notes":"v85 evidence pins the released V41-C lane on main: canonical adeu_architecture_observation_frame@1 over the released V41-A request boundary and V41-B settlement carry-through, facts-only observed extraction, exact provenance closure, direct-vs-derived marking, explicit unresolved observations, and continued compile entitlement blocking without intended/alignment/remediation creep.","observation_fixture_hash":"82bb14c4ed88cd079c0ff231803c1a1a6f5babdb961afeb285c69278bf7d529f","observation_fixture_path":"apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_observation_frame_v85_reference.json","observation_frame_id":"v41c_v85_architecture_ir_observation_reference","observation_schema_reference_hash":"fa4948aca62815057b9b2cf19e19e06a0af830868697aa2b41f43ac6f86e4f4d","observation_schema_reference_mirror_hash":"fa4948aca62815057b9b2cf19e19e06a0af830868697aa2b41f43ac6f86e4f4d","observation_schema_reference_mirror_matches_authoritative":true,"observation_schema_reference_mirror_path":"spec/adeu_architecture_observation_frame.schema.json","observation_schema_reference_path":"packages/adeu_architecture_compiler/schema/adeu_architecture_observation_frame.v1.json","observed_authority_source_count":2,"observed_boundary_count":1,"observed_evidence_hook_count":2,"observed_observability_hook_count":2,"observed_unit_count":5,"observed_workflow_count":1,"package_surface_hash":"2eb5c235fc9682c5e0a457d710bb935eb6394f8baf1c095b1cdc67bf8396a24e","package_surface_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py","policy_sources":[{"path":"AGENTS.md","sha256":"4ee9bbb70d02036e72deaaba7348a3b7e8d93b0a7431535a4597be08b7af7f93"},{"path":"docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md","sha256":"211d0c2e5610b0e0a7d99024b34a6c1fcda909b1cefd7b8408976af50aa9ce9d"},{"path":"docs/DRAFT_NEXT_ARC_OPTIONS_v23.md","sha256":"ecba0cc429e0c2acba42123eb6d5c21525fe7b06fe4429269785a9c4fdac5379"},{"path":"docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md","sha256":"70a6e8bf556cb51a1ceaff00502f7b8807c54a353a067e76cef00e1b7396dd23"},{"path":"docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md","sha256":"78dafff2680614505e6b79fe03d0f34223f7cfe0d8366bd1f9aa2df497731dee"}],"provenance_closure_verified":true,"request_boundary_consumption_verified":true,"runtime_observability_comparison_ref":"artifacts/agent_harness/v85/evidence_inputs/runtime_observability_comparison_v85.json","schema":"v41c_architecture_observation_frame_evidence@1","schema_export_source_hash":"6718bd1e164a6d7b094b00ec995a0e8a90c3f235a26e73058490ea2c01bb2e5f","schema_export_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py","settlement_boundary_consumption_verified":true,"settlement_fixture_hash":"8db1d0c2854d0f3ab55a1d155f521ebdb3b0ecda72242b19f10ac9621b1f38aa","settlement_fixture_path":"apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_analysis_settlement_frame_v85_observation_derivative.json","settlement_frame_id":"v41b_v85_architecture_ir_observation_settlement_derivative","settlement_frame_ref":"apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_analysis_settlement_frame_v85_observation_derivative.json","source_set_hash":"0420b6ef8626fb4e5fdecec355952857554499d13fda12d798e4e5570b62278e","unresolved_observation_count":1,"unresolved_observation_preservation_verified":true,"unresolved_reason_kinds":["requires_non_source_context"],"unresolved_reason_typing_verified":true,"upstream_blocking_ref_count":2,"upstream_compile_entitlement":"blocked"}
```

## Recommendation (Post v85)

- gate decision:
  - `V41C_ARCHITECTURE_OBSERVATION_FRAME_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v85 closes the bounded `V41-C` baseline with canonical
    `adeu_architecture_observation_frame@1`, exact consumption of the released
    `V41-A` request boundary and `V41-B` settlement carry-through, facts-only
    observed extraction, explicit direct-vs-derived marking, grounded provenance
    closure, and fail-closed unresolved-observation preservation integrated on
    `main`.
  - the released lane remains explicitly bounded to observation only: no intended
    compile, alignment report, runner release, remediation planning, or repo mutation
    behavior shipped in v85.
  - the committed reference fixture remains honestly `blocked`, preserving the exact
    lesson this slice was meant to lock: observed extraction may proceed over a
    frozen request world and settlement frame without laundering that blocked
    settlement posture into earned compile authority.
  - no stop-gate schema-family or metric-key regressions were introduced by the lane;
    runtime observability changed only informationally, and the planned `V41-C`
    facts-only observation baseline is now complete on `main` at its intentionally
    bounded scope.
