# Draft Stop-Gate Decision (Post vNext+87)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md`

Status: draft decision note (post-hoc closeout capture, March 26, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS87.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v87_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+87` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md`.
- This note captures `V41-E` practical alignment closeout evidence only; it does not
  authorize CLI runner release, remediation or repo-mutation planning, merged-truth
  reconciliation, API/web inspection routes, checkpoint/projection/UX practical
  outputs, or any practical orchestration authority outside the bounded alignment
  lane.
- Canonical `V41-E` release in v87 is carried by the extended
  `packages/adeu_architecture_compiler` alignment surface, deterministic helper
  coverage in `packages/adeu_architecture_compiler/tests/`, the committed alignment
  fixture ladder under `apps/api/fixtures/architecture/vnext_plus87/`, and the
  canonical `v41e_architecture_alignment_report_evidence@1` evidence input under
  `artifacts/agent_harness/v87/evidence_inputs/`.
- The released v87 lane remains intentionally bounded: exact consumption of the
  released `V41-A` request boundary, `V41-B` settlement frame, `V41-C` observation
  frame, and `V41-D` intended semantic IR; authoritative comparison against
  `adeu_architecture_semantic_ir@1`; stable finding-id derivation over canonical
  typed support tuples; explicit severity and blocking posture; and unresolved
  unknown carry-through remain authoritative.
- Supporting downstream fixture refreshes in the merged PR remain replay-preserving
  maintenance only; they do not widen the released `V41-E` semantic scope.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `637e8a78718bc0094c8ed339b85d9444dd012e6a`
- arc-completion CI runs:
  - PR `#309`
    - head commit: `2c558853a7937a6f5c8974a4bb3d8c314ead2d44`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23593484791`
    - conclusion: `success`
  - branch push before merge
    - head commit: `2c558853a7937a6f5c8974a4bb3d8c314ead2d44`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23593483211`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `637e8a78718bc0094c8ed339b85d9444dd012e6a`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23594836822`
    - conclusion: `success`
- merged implementation PRs:
  - `#309` (`Implement v87 alignment report lane`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v87_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v87_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v87_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v87/evidence_inputs/metric_key_continuity_assertion_v87.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v87/evidence_inputs/runtime_observability_comparison_v87.json`
  - `V41-E` alignment evidence input:
    `artifacts/agent_harness/v87/evidence_inputs/v41e_architecture_alignment_report_evidence_v87.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v87/runtime/evidence/codex/copilot/v87-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v87/runtime/evidence/codex/copilot/v87-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v87 remains carried by the typed
    alignment implementation, exact request/settlement/observation/intended
    consumption, stable finding-id derivation, committed fixture replay, unresolved
    unknown carry-through, and the closeout quality and stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS87_EDGES.md`

## Exit-Criteria Check (vNext+87)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V41-E` merged with green CI | required | `pass` | PR `#309`, merge commit `637e8a78718bc0094c8ed339b85d9444dd012e6a`, Actions runs `23593484791`, `23593483211`, and `23594836822` |
| Canonical alignment helpers ship without redefining released upstream schema families | required | `pass` | `alignment.py`, `adeu_architecture_alignment_report.v1.json`, `spec/adeu_architecture_alignment_report.schema.json`, and `test_v41e_alignment_fixture_replays_and_validates` |
| Exact `V41-A` request-bound replay remains enforced | required | `pass` | `analysis_request_ref = apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_analysis_request_v87_alignment_derivative.json`, `analysis_request_id = v41a_v86_architecture_ir_intended_request_derivative`, `source_set_hash = 4509271c7ba8e3333c869c8e2bd4256eff5a8d76cb822c5c4d28c5a3e6ee8ade`, and `request_boundary_consumption_verified = true` |
| Exact `V41-B` settlement entitlement is consumed as-is and not recomputed locally | required | `pass` | `settlement_frame_ref = apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json`, `compile_entitlement = entitled`, `compile_entitlement_consumed_as_is = true`, and `test_v41e_rejects_blocked_settlement_world` |
| Exact `V41-C` observation frame is consumed without lane collapse | required | `pass` | `observation_frame_ref = apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_observation_frame_v87_alignment_derivative.json`, `observation_boundary_consumption_verified = true`, `intended_observed_lane_separation_verified = true`, and `observation_constrains_but_does_not_mint_truth_verified = true` |
| Released `adeu_architecture_semantic_ir@1` remains the authoritative intended comparison surface | required | `pass` | `semantic_ir_ref = apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_semantic_ir_v87_alignment_derivative.json`, `authoritative_intended_surface = adeu_architecture_semantic_ir@1`, and `semantic_ir_authoritative_surface_verified = true` |
| Stable finding ids and deterministic dedup/order remain enforced | required | `pass` | `finding_ids = [\"ALIGN-UNK-5a2cc657\"]`, `finding_id_derivation_verified = true`, `canonical_dedup_and_order_verified = true`, and `test_v41e_rejects_finding_id_drift` |
| Findings remain grounded in typed upstream refs rather than prose-only support | required | `pass` | `prose_only_support_rejected = true`, `test_v41e_rejects_prose_only_finding_support`, and no finding support paths escape the released request/settlement surfaces |
| Unresolved upstream unknowns remain explicit in the alignment report | required | `pass` | `alignment_posture = blocked`, `blocking_finding_ids = [\"ALIGN-UNK-5a2cc657\"]`, `unresolved_unknown_carrythrough_verified = true`, and `test_v41e_alignment_fixture_replays_and_validates` |
| Aligned posture is only legal when there are no findings | required | `pass` | `test_v41e_can_emit_aligned_report_when_no_findings_remain`, `finding_count = 1` on the accepted ladder, and `alignment_posture = blocked` |
| Remediation, runner, and merged-truth creep remain deferred | required | `pass` | `downstream_runner_remediation_deferred = true`, no such outputs under `apps/api/fixtures/architecture/vnext_plus87/`, and no such outputs claimed by `alignment.py` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v87_closeout.json` keeps `schema = "stop_gate_metrics@1"`, `valid = true`, and `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v87/evidence_inputs/metric_key_continuity_assertion_v87.json` records exact keyset equality versus v86 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v87/evidence_inputs/runtime_observability_comparison_v87.json` |

## Stop-Gate Summary

```json
{
  "schema": "v87_closeout_stop_gate_summary@1",
  "arc": "vNext+87",
  "target_path": "V41-E",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v86": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 99,
  "runtime_observability_delta_ms": -2
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v86_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v87_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+86","baseline_elapsed_ms":101,"baseline_source":"artifacts/stop_gate/report_v86_closeout.md","current_arc":"vNext+87","current_elapsed_ms":99,"current_source":"artifacts/stop_gate/report_v87_closeout.md","delta_ms":-2,"notes":"v87 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V41-E deterministic alignment lane over released request, settlement, observation, and intended artifacts, with stable finding ids, unresolved-unknown carry-through, and no runner/remediation/merged-truth widening.","schema":"runtime_observability_comparison@1"}
```

## V41E Alignment Evidence

```json
{"alignment_fixture_hash":"b2b5ae91423795d62d5a96e5116d2d03281afae5dd09129eddb016a9e5763207","alignment_fixture_path":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_alignment_report_v87_reference.json","alignment_posture":"blocked","alignment_report_id":"v41e_v87_packages_adeu_architecture_ir_src_adeu_architecture_ir_alignment_report","alignment_schema_reference_hash":"20de771cbb763a73f02625db48b77d99ad11c4b4e09c350b59b6e0d0410568a7","alignment_schema_reference_mirror_hash":"20de771cbb763a73f02625db48b77d99ad11c4b4e09c350b59b6e0d0410568a7","alignment_schema_reference_mirror_matches_authoritative":true,"alignment_schema_reference_mirror_path":"spec/adeu_architecture_alignment_report.schema.json","alignment_schema_reference_path":"packages/adeu_architecture_compiler/schema/adeu_architecture_alignment_report.v1.json","analysis_request_fixture_hash":"4b50d67b51a6833861d217bf60381c74aa73421eedb9ccfeee239539ff820884","analysis_request_fixture_path":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_analysis_request_v87_alignment_derivative.json","analysis_request_id":"v41a_v86_architecture_ir_intended_request_derivative","analysis_request_ref":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_analysis_request_v87_alignment_derivative.json","architecture_id":"asir_v86_packages_adeu_architecture_ir_src_adeu_architecture_ir_repo_grounded_compile","basis_kinds":["unresolved_upstream_unknown"],"blocking_finding_ids":["ALIGN-UNK-5a2cc657"],"canonical_dedup_and_order_verified":true,"canonical_replay_verified":true,"compile_entitlement_consumed_as_is":true,"contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md#v41e_practical_analysis_alignment_contract@1","downstream_runner_remediation_deferred":true,"evidence_input_path":"artifacts/agent_harness/v87/evidence_inputs/v41e_architecture_alignment_report_evidence_v87.json","export_test_reference_hash":"8c86100817cfefc4c91a9c8593a7bfc0c44cd9c457531f24386ba2c3078ea841","export_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py","finding_count":1,"finding_id_derivation_verified":true,"finding_ids":["ALIGN-UNK-5a2cc657"],"implementation_source_hash":"de69836283dda5afd024bdbda75127ac022181be7be816a1678a2f5016deca76","implementation_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/alignment.py","intended_observed_lane_separation_verified":true,"merge_commit":"637e8a78718bc0094c8ed339b85d9444dd012e6a","merged_pr":"#309","metric_key_cardinality":80,"metric_key_exact_set_equal_v86":true,"mismatch_classes":["unresolved_unknown"],"model_test_reference_hash":"5b9f125dcbb380c96270995e24299b86245f9e032b87f41d627991d002c07315","model_test_reference_path":"packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41e.py","notes":"v87 evidence pins the released V41-E lane on main: canonical adeu_architecture_alignment_report@1 over the released V41-A request boundary, V41-B settlement frame, V41-C observation frame, and V41-D intended semantic IR, with stable finding ids, explicit severity and blocking posture, unresolved-unknown carry-through, and no runner/remediation/merged-truth widening.","observation_boundary_consumption_verified":true,"observation_constrains_but_does_not_mint_truth_verified":true,"observation_fixture_hash":"f9031ecd189ea4373566ffd7bcebb6cfc59f047eaf9243948329bb87825e3717","observation_fixture_path":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_observation_frame_v87_alignment_derivative.json","observation_frame_id":"v41c_v86_architecture_ir_intended_observation_derivative","observation_frame_ref":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_observation_frame_v87_alignment_derivative.json","package_surface_hash":"8c3fc045c0f5b7dc5aed2d6bbb4f13bdde1497bdda2c52e477a18022df6484b8","package_surface_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py","policy_sources":[{"path":"AGENTS.md","sha256":"4ee9bbb70d02036e72deaaba7348a3b7e8d93b0a7431535a4597be08b7af7f93"},{"path":"docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md","sha256":"f9ee27a26150e51232616bd243074151849b18a2227377fdd3f1cf4f639c431e"},{"path":"docs/DRAFT_NEXT_ARC_OPTIONS_v23.md","sha256":"3844c946a7a5eb9148ce5d1eff040345bd7681f5d3e347fe11a5c27f2cfa80f9"},{"path":"docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md","sha256":"a281c05fe5f9b7c5fecde378f595641d6710626e7b61b18005509c7498bafeab"},{"path":"docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md","sha256":"da627f43118aacd4f16d1dec5fa173ac0ab37e9d4c94e64776d7da7d58fe118b"}],"prose_only_support_rejected":true,"request_boundary_consumption_verified":true,"runtime_observability_comparison_ref":"artifacts/agent_harness/v87/evidence_inputs/runtime_observability_comparison_v87.json","schema":"v41e_architecture_alignment_report_evidence@1","schema_export_source_hash":"dc2bc56d62868b4b20e5c77432788af628ad287b37235355670409ec29c28486","schema_export_source_path":"packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py","semantic_hash":"ab9e6a16428a5fd7ab1c657c6f018a122458e3bd45f5a7db72298c4470f7d474","semantic_ir_authoritative_surface_verified":true,"semantic_ir_fixture_hash":"4237e7687dce7db9130dd7ed13e5c2a10ca9dc83e10a87b7b8db8ac2e9131ca7","semantic_ir_fixture_path":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_semantic_ir_v87_alignment_derivative.json","settlement_boundary_consumption_verified":true,"settlement_fixture_hash":"a48a2c70fbc724d2ada8a1f69796b85d1794d2b04d89af113c8cd0db1be7c1ac","settlement_fixture_path":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json","settlement_frame_id":"v41b_v86_architecture_ir_intended_settlement_derivative","settlement_frame_ref":"apps/api/fixtures/architecture/vnext_plus87/adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json","severity_counts":{"advisory":0,"blocking":1,"warning":0},"source_set_hash":"4509271c7ba8e3333c869c8e2bd4256eff5a8d76cb822c5c4d28c5a3e6ee8ade","supporting_replay_refreshes":[{"path":"apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json","sha256":"71eab13a169c9416bc6bf2e74244960c354e930e79fab610e181fd041fa6db96"},{"path":"apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_human_needed_reference.json","sha256":"efff1724acb2df86740d8c1128f89e65c5522f239e359e2d8c81d68d06146336"},{"path":"apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_checkpoint_trace_v79_oracle_reference.json","sha256":"a3069e3aa26b7661d87a0ea982bf02b2b0137ae362612d49e7aa11ef88cb0283"},{"path":"apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_ir_delta_v79_reference.json","sha256":"7ea935d5aa7cc01b5c763f940d2c8f2753f04edf91013311223dd6ae1dfd101d"},{"path":"apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_request_v79_reference.json","sha256":"b35563d6ed480b49fed8f3a34f1bbc26e9029c87fb05f64e937990bf968c88cb"},{"path":"apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_resolution_v79_reference.json","sha256":"263bab3e38f29d2e977ccda0e78899453c2e20a99ed72e6d7427292b8e91a105"},{"path":"apps/api/fixtures/architecture/vnext_plus82/v40f_architecture_release_integration_evidence_v82_reference.json","sha256":"1bbd864575aaf1b5c422411acae149aa9e7b4f66593d86150d4d9c3332748682"},{"path":"artifacts/agent_harness/v82/evidence_inputs/v40f_architecture_release_integration_evidence_v82.json","sha256":"1bbd864575aaf1b5c422411acae149aa9e7b4f66593d86150d4d9c3332748682"},{"path":"apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_analysis_request_v86_intended_derivative.json","sha256":"6bd8abb367a2428e9ceb20b00b56984a9ffa1c630d0b9429c9afcfbd225f9260"},{"path":"apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json","sha256":"3afd4075e5aac925e237e3d9a240a1dd1c78c9ca84e943feb24115664ca4237e"},{"path":"apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_intent_packet_v86_reference.json","sha256":"2c5c0146261dbc36350db46dc9d8b27946106afb626f55f26ce5103acf116e3d"},{"path":"apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_observation_frame_v86_intended_derivative.json","sha256":"a6ec5da05f881bdd84cef56e7eb9481267b610b3d63b91dd47197604ef8212a3"},{"path":"apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_semantic_ir_v86_reference.json","sha256":"4237e7687dce7db9130dd7ed13e5c2a10ca9dc83e10a87b7b8db8ac2e9131ca7"},{"path":"apps/api/fixtures/architecture/vnext_plus86/adeu_architecture_world_hypothesis_v86_reference.json","sha256":"60fe99bde600138b2203624575b993a2221e1c92bb0775e3859987d0776e2f61"}],"unresolved_unknown_carrythrough_verified":true}
```

## Recommendation (Post v87)

- gate decision:
  - `V41E_ARCHITECTURE_ALIGNMENT_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v87 closes the bounded `V41-E` baseline with canonical deterministic alignment
    over the released `V41-A` request boundary, `V41-B` settlement frame, `V41-C`
    observation frame, and `V41-D` intended semantic IR integrated on `main`.
  - the released lane remains explicitly bounded to alignment only: no runner
    orchestration, remediation planning, repo mutation, merged-truth reconciliation,
    or downstream checkpoint/projection/UX practical surfaces shipped in v87.
  - the committed reference fixture demonstrates the exact lesson this slice was
    meant to lock: intended and observed architecture can be compared
    deterministically without observation silently becoming the hidden source of
    intended truth, while unresolved upstream unknowns remain explicit as blocking
    alignment findings.
  - no stop-gate schema-family or metric-key regressions were introduced by the
    lane; runtime observability changed only informationally, and the planned `V41-E`
    deterministic alignment baseline is now complete on `main` at its intentionally
    bounded scope.
