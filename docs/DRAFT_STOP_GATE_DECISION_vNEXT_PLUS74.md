# Draft Stop-Gate Decision (Post vNext+74)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md`

Status: draft decision note (post-hoc closeout capture, March 22, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS74.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v74_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+74` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md`.
- This note captures `V39-C` synthetic pressure-mismatch observation and conformance
  closeout evidence only; it does not authorize fix-plan rollout, automatic repo
  mutation, hybrid oracle execution, workflow-blocking policy automation, or any
  broader repo-wide scanning surface by itself.
- Canonical `V39-C` release in v74 is carried by canonical
  `synthetic_pressure_mismatch_observation_packet@1`, canonical
  `synthetic_pressure_mismatch_conformance_report@1`, authoritative and mirrored schema
  exports under `packages/adeu_core_ir/schema/` and `spec/`, committed v74
  subject/packet/report fixtures, and canonical
  `v39c_synthetic_pressure_mismatch_observation_evidence@1`.
- The released v74 lane remains intentionally bounded:
  it consumes the released `V39-B` registry rather than redefining it, executes only
  deterministic-local rules, keeps every observation packet single-subject, keeps
  conformance aggregation count-based and list-based, keeps
  `safe_autofix_candidates` candidate-only, preserves anti-authorship and anti-score
  posture, and treats `resolution_route` as carried-through metadata rather than proof
  that `V39-E` adjudication exists.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `cd2abd81d9e33a5a2797de89147c4f80842bfd6a`
- arc-completion CI runs:
  - PR `#296`
    - head commit: `72fe3c7b46f9d9aab750c38670b9657c9e373c53`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23397018752`
    - conclusion: `success`
  - branch push before merge
    - head commit: `72fe3c7b46f9d9aab750c38670b9657c9e373c53`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23397017873`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `cd2abd81d9e33a5a2797de89147c4f80842bfd6a`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23397089059`
    - conclusion: `success`
- merged implementation PRs:
  - `#296` (`Implement V39-C observation report baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v74_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v74_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v74_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v74/evidence_inputs/metric_key_continuity_assertion_v74.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v74/evidence_inputs/runtime_observability_comparison_v74.json`
  - V39-C observation evidence input:
    `artifacts/agent_harness/v74/evidence_inputs/v39c_synthetic_pressure_mismatch_observation_evidence_v74.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v74/runtime/evidence/codex/copilot/v74-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v74/runtime/evidence/codex/copilot/v74-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v74 remains carried by the typed
    observation/report/schema/fixture artifacts plus the closeout quality and
    stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS74_EDGES.md`

## Exit-Criteria Check (vNext+74)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V39-C` merged with green CI | required | `pass` | PR `#296`, merge commit `cd2abd81d9e33a5a2797de89147c4f80842bfd6a`, Actions runs `23397018752` and `23397089059` |
| Canonical `synthetic_pressure_mismatch_observation_packet@1` validates and exports cleanly | required | `pass` | `packages/adeu_core_ir/schema/synthetic_pressure_mismatch_observation_packet.v1.json`, `spec/synthetic_pressure_mismatch_observation_packet.schema.json`, and `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_observation.py` |
| Canonical `synthetic_pressure_mismatch_conformance_report@1` validates and exports cleanly | required | `pass` | `packages/adeu_core_ir/schema/synthetic_pressure_mismatch_conformance_report.v1.json`, `spec/synthetic_pressure_mismatch_conformance_report.schema.json`, and `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_observation.py` |
| Positive deterministic-local finding replay is preserved | required | `pass` | `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/synthetic_pressure_mismatch_observation_packet_v74_positive.json` and `test_v39c_positive_observation_fixture_validates_and_replays` |
| Valid no-finding packet/report replay is preserved | required | `pass` | `synthetic_pressure_mismatch_observation_packet_v74_no_findings.json`, `synthetic_pressure_mismatch_conformance_report_v74_no_findings.json`, and the corresponding replay tests |
| Unsupported execution requests fail closed | required | `pass` | `synthetic_pressure_mismatch_unsupported_execution_request_v74.json` and `test_v39c_requested_unsupported_rule_fails_closed` |
| Released deterministic rule support is not overclaimed for unsupported subject kinds | required | `pass` | `test_v39c_fails_closed_for_registry_applicable_but_detector_unsupported_subject` and `v39c_synthetic_pressure_mismatch_observation_evidence_v74.json` |
| Carried-through finding metadata matches the released registry rule exactly | required | `pass` | `test_v39c_packet_rejects_shadow_registry_metadata_drift` and `v39c_synthetic_pressure_mismatch_observation_evidence_v74.json` |
| Observation packets remain single-subject and reject exact duplicate finding identity tuples | required | `pass` | packet fixtures, `test_v39c_packet_rejects_duplicate_finding_identity`, and `v39c_synthetic_pressure_mismatch_observation_evidence_v74.json` |
| Conformance reports remain count-based/list-based and bind finding refs to the aggregated packet set | required | `pass` | report fixtures, `test_v39c_report_rejects_finding_refs_outside_aggregated_packet_set`, and `v39c_synthetic_pressure_mismatch_observation_evidence_v74.json` |
| Multi-packet report ids are derived from the packet set | required | `pass` | `test_v39c_multi_packet_report_id_is_derived_from_packet_set` and `synthetic_pressure_mismatch_conformance_report_v74_reference.json` |
| `safe_autofix_candidates` remain report-level candidates only and the report stays anti-score by construction | required | `pass` | report schema/fixtures plus `test_v39c_report_rejects_non_literal_posture` and `v39c_synthetic_pressure_mismatch_observation_evidence_v74.json` |
| Authorship/origin remain outside the governed object | required | `pass` | `v39c_synthetic_pressure_mismatch_observation_evidence_v74.json` and the released `V39-C` schema/model vocabulary |
| Subject inputs remain committed local fixtures only | required | `pass` | all v74 subject/packet/report fixtures remain under `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v74_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v74/evidence_inputs/metric_key_continuity_assertion_v74.json` records exact keyset equality versus v73 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v74/evidence_inputs/runtime_observability_comparison_v74.json` |

## Stop-Gate Summary

```json
{
  "schema": "v74_closeout_stop_gate_summary@1",
  "arc": "vNext+74",
  "target_path": "V39-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v73": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v73_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v74_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+73","baseline_elapsed_ms":96,"baseline_source":"artifacts/stop_gate/report_v73_closeout.md","current_arc":"vNext+74","current_elapsed_ms":96,"current_source":"artifacts/stop_gate/report_v74_closeout.md","delta_ms":0,"notes":"v74 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V39-C synthetic pressure-mismatch observation and conformance lane.","schema":"runtime_observability_comparison@1"}
```

## V39C Synthetic Pressure-Mismatch Observation Evidence

```json
{
  "aggregate_ref_membership_verified": true,
  "anti_authorship_boundary_preserved": true,
  "anti_score_boundary_preserved": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md#v39c_synthetic_pressure_mismatch_observation_contract@1",
  "deterministic_local_only_preserved": true,
  "evidence_input_path": "artifacts/agent_harness/v74/evidence_inputs/v39c_synthetic_pressure_mismatch_observation_evidence_v74.json",
  "evaluator_id": "adeu_core_ir.synthetic_pressure_mismatch_observation.derive_v39c_observation_packet@1",
  "evaluator_version": "1",
  "implementation_source_hash": "efae54e20c33e7a894dde8e2b6a1e312aa3f47c44e66021a1f3a5551aa8b54a6",
  "implementation_source_path": "packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch_observation.py",
  "notes": "v74 evidence pins the released observation/report schemas, subject and packet fixtures, no-finding and unsupported-execution coverage, and the bounded V39-C anti-authorship / anti-score contract on main.",
  "observation_schema_reference_hash": "12878c4d237be0eac69cee65f7e44f5bfb31cf805d178af0ff8a6614208d102e",
  "observation_schema_reference_path": "packages/adeu_core_ir/schema/synthetic_pressure_mismatch_observation_packet.v1.json",
  "policy_sources": [
    {
      "path": "AGENTS.md",
      "sha256": "4ee9bbb70d02036e72deaaba7348a3b7e8d93b0a7431535a4597be08b7af7f93"
    },
    {
      "path": "docs/DRAFT_SYNTHETIC_PRESSURE_MISMATCH_DRIFT_v0.md",
      "sha256": "63d36a286e0a6fa027209e7fc77377593deef80b71bf50fe495a25d8bcca55c5"
    },
    {
      "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS74.md",
      "sha256": "cd7139e6ba7a331c36bc38744549a344db5db14dcb9237a88357051ee69b1fd5"
    }
  ],
  "report_schema_reference_hash": "f1655c2e832c126899340e90488b54e973d376d0a2f49c21980b3d1a8084bab6",
  "report_schema_reference_path": "packages/adeu_core_ir/schema/synthetic_pressure_mismatch_conformance_report.v1.json",
  "schema": "v39c_synthetic_pressure_mismatch_observation_evidence@1",
  "schema_export_parity_verified": true,
  "single_subject_packet_scope_preserved": true,
  "verification_passed": true
}
```

## Recommendation (Post v74)

- gate decision:
  - `V39C_SYNTHETIC_PRESSURE_MISMATCH_OBSERVATION_COMPLETE_ON_MAIN`
- rationale:
  - v74 closes the bounded `V39-C` baseline with canonical
    `synthetic_pressure_mismatch_observation_packet@1`, canonical
    `synthetic_pressure_mismatch_conformance_report@1`, authoritative/mirrored schema
    exports, committed v74 subject/packet/report fixtures, and canonical
    `v39c_synthetic_pressure_mismatch_observation_evidence@1` integrated on `main`.
  - the released lane remains explicitly bounded to deterministic-local observation and
    count-based conformance aggregation; it does not widen into fix plans, repo
    mutation, hybrid adjudication, authorship classification, or repo-wide crawling.
  - review-driven hardening on the merged PR now preserves fail-closed handling for
    unsupported subject kinds, aggregated-packet ref integrity, and stable
    packet-set-derived report ids.
  - no stop-gate schema-family, metric-key, or runtime-observability regressions were
    introduced by the lane.
