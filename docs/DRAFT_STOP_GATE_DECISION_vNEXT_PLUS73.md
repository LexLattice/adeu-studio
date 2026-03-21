# Draft Stop-Gate Decision (Post vNext+73)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`

Status: draft decision note (post-hoc closeout capture, March 21, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS73.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v73_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+73` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`.
- This note captures `V39-B` synthetic pressure-mismatch registry closeout evidence
  only; it does not authorize detector rollout, observation packets, fix-plan
  execution, hybrid oracle adjudication, merge-worthiness scoring, or any broader
  runtime widening surface by itself.
- Canonical `V39-B` release in v73 is carried by canonical
  `synthetic_pressure_mismatch_rule_registry@1`, the authoritative schema export under
  `packages/adeu_core_ir/schema/`, the mirrored schema under `spec/`, and the
  committed v73 reference fixture.
- The released v73 registry remains intentionally bounded:
  it governs pressure-mismatch drift rather than author/model identity, stays
  anti-score by construction, remains registry-local in vocabulary, keeps first-slice
  package placement in `adeu_core_ir`, and treats `resolution_route` as metadata
  rather than proof of an already-shipped adjudication runtime.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `6cf19fe0e86074bd1e5bf204288cf9aa1165153d`
- arc-completion CI runs:
  - PR `#295`
    - head commit: `a6bc6386eb4af921e1fddae28d083a80c0817f58`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23388482218`
    - conclusion: `success`
  - branch push before merge
    - head commit: `a6bc6386eb4af921e1fddae28d083a80c0817f58`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23388481462`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `6cf19fe0e86074bd1e5bf204288cf9aa1165153d`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23388578129`
    - conclusion: `success`
- merged implementation PRs:
  - `#295` (`Implement V39-B pressure-mismatch registry`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v73_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v73_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v73_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v73/evidence_inputs/metric_key_continuity_assertion_v73.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v73/evidence_inputs/runtime_observability_comparison_v73.json`
  - V39-B registry evidence input:
    `artifacts/agent_harness/v73/evidence_inputs/v39b_synthetic_pressure_mismatch_registry_evidence_v73.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v73/runtime/evidence/codex/copilot/v73-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v73/runtime/evidence/codex/copilot/v73-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v73 remains carried by the typed
    registry/schema/fixture artifacts plus the closeout quality and stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS73_EDGES.md`

## Exit-Criteria Check (vNext+73)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V39-B` merged with green CI | required | `pass` | PR `#295`, merge commit `6cf19fe0e86074bd1e5bf204288cf9aa1165153d`, Actions runs `23388482218` and `23388578129` |
| Canonical `synthetic_pressure_mismatch_rule_registry@1` validates and exports cleanly | required | `pass` | `packages/adeu_core_ir/schema/synthetic_pressure_mismatch_rule_registry.v1.json`, `spec/synthetic_pressure_mismatch_rule_registry.schema.json`, and `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py` |
| Committed reference registry fixture revalidates deterministically | required | `pass` | `apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/synthetic_pressure_mismatch_rule_registry_v73_reference.json`, `packages/adeu_core_ir/tests/test_synthetic_pressure_mismatch_registry.py` |
| `signal_kind`, `subject_kind`, `evidence_mode`, `evidence_regime`, `allowed_action`, `resolution_route`, and `expected_utility_gain` remain bounded vocabularies | required | `pass` | `packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch.py` and exported schemas |
| Registry entries declare rule applicability law only | required | `pass` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md` plus `SyntheticPressureMismatchRuleRegistry` root shape |
| `applicable_subject_kinds`, `expected_utility_gains`, and `rules` are non-empty at schema level | required | `pass` | exported schemas now encode `minItems: 1`; replayed in `test_synthetic_pressure_mismatch_registry.py` |
| `counterexample_policy` is required and structurally bounded | required | `pass` | `SyntheticPressureMismatchCounterexamplePolicy` and `v39b_synthetic_pressure_mismatch_registry_evidence_v73.json` |
| Authorship/origin remain outside the governed object | required | `pass` | `test_v39b_registry_rejects_authorship_signal_kind` and `v39b_synthetic_pressure_mismatch_registry_evidence_v73.json` |
| Registry remains anti-score by construction | required | `pass` | no posture scalar or merge-worthiness field exists in schema/model/fixture |
| `safe_autofix` remains blocked for ambiguous, meta-governance, and first-slice shape-regularity rules | required | `pass` | runtime validators in `synthetic_pressure_mismatch.py` and schema-level `allOf`/`not` constraints in the exported schema |
| Any `safe_autofix` rule also requires deterministic-local evidence and deterministic-only routing | required | `pass` | runtime validators and schema-level `if/then` constraints in the exported schema |
| Package placement remains `adeu_core_ir` and vocabulary remains registry-local | required | `pass` | `docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md`, schema/model exports, and `v39b_synthetic_pressure_mismatch_registry_evidence_v73.json` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v73_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v73/evidence_inputs/metric_key_continuity_assertion_v73.json` records exact keyset equality versus v72 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v73/evidence_inputs/runtime_observability_comparison_v73.json` |

## Stop-Gate Summary

```json
{
  "schema": "v73_closeout_stop_gate_summary@1",
  "arc": "vNext+73",
  "target_path": "V39-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v72": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": -9
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v72_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v73_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+72","baseline_elapsed_ms":105,"baseline_source":"artifacts/stop_gate/report_v72_closeout.md","current_arc":"vNext+73","current_elapsed_ms":96,"current_source":"artifacts/stop_gate/report_v73_closeout.md","delta_ms":-9,"notes":"v73 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V39-B synthetic pressure-mismatch registry lane.","schema":"runtime_observability_comparison@1"}
```

## V39B Synthetic Pressure-Mismatch Registry Evidence

```json
{
  "authorship_boundary_preserved": true,
  "authoritative_schema_reference_hash": "ba8316eec5c90a9e0b2817dcd53a86b56b2ac2b42efe7692682ff9f59c2ce64e",
  "authoritative_schema_reference_path": "packages/adeu_core_ir/schema/synthetic_pressure_mismatch_rule_registry.v1.json",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md#v39b_synthetic_pressure_mismatch_registry_contract@1",
  "counterexample_policy_structured": true,
  "evaluator_id": "adeu_core_ir.synthetic_pressure_mismatch.SyntheticPressureMismatchRuleRegistry@1",
  "evaluator_version": "1",
  "evidence_input_path": "artifacts/agent_harness/v73/evidence_inputs/v39b_synthetic_pressure_mismatch_registry_evidence_v73.json",
  "expected_utility_gain_vocabulary_bounded": true,
  "fixture_reference_hash": "fe47ddb2bb072be3b19d4aafdf1d70921ead64dea41633ac8ba86d4fcd6ff105",
  "fixture_reference_path": "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus73/synthetic_pressure_mismatch_rule_registry_v73_reference.json",
  "implementation_source_hash": "ddd45215da9501f68bd7de936dd8868d9f20679589c5c98046baa65723eb695c",
  "implementation_source_path": "packages/adeu_core_ir/src/adeu_core_ir/synthetic_pressure_mismatch.py",
  "mirror_schema_reference_hash": "ba8316eec5c90a9e0b2817dcd53a86b56b2ac2b42efe7692682ff9f59c2ce64e",
  "mirror_schema_reference_path": "spec/synthetic_pressure_mismatch_rule_registry.schema.json",
  "notes": "v73 evidence pins the first released synthetic pressure-mismatch registry fixture, authoritative and mirrored schema hashes, and the bounded V39-B anti-authorship / anti-score contract on main.",
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
      "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS73.md",
      "sha256": "fd915a0853764842007a0599e93e85eb2fc6663e67f9705c87be445d9fd791f3"
    }
  ],
  "registry_only_scope_preserved": true,
  "safe_autofix_schema_constraints_verified": true,
  "schema": "v39b_synthetic_pressure_mismatch_registry_evidence@1",
  "schema_export_parity_verified": true,
  "seed_rules_cover_all_five_signal_families": true,
  "verification_passed": true
}
```

## Recommendation (Post v73)

- gate decision:
  - `V39B_SYNTHETIC_PRESSURE_MISMATCH_REGISTRY_COMPLETE_ON_MAIN`
- rationale:
  - v73 closes the bounded `V39-B` registry slice with canonical
    `synthetic_pressure_mismatch_rule_registry@1`, authoritative/mirrored schema
    exports, one committed v73 reference registry fixture, and replayed schema/model
    guard coverage integrated on `main`.
  - the registry remains explicitly bounded to pressure-mismatch rule law and does not
    widen into detectors, observation packets, fix plans, or hybrid adjudication.
  - schema-level closeout hardening now preserves the non-empty-array law and the
    first-slice `safe_autofix` contract even for schema-only validator consumers.
  - no stop-gate schema-family, metric-key, or runtime-observability regressions were
    introduced by the lane.
