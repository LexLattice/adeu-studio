# Draft Stop-Gate Decision (Post vNext+72)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md`

Status: draft decision note (post-hoc closeout capture, March 21, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS72.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v72_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+72` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md`.
- This note captures `V39-A` retrospective external-contribution alignment closeout
  evidence only; it does not authorize automatic merge-worthiness judgment, automatic
  policy adoption, automatic imported-history rewriting, automatic repo mutation, or
  any broader all-module conformance marketplace by itself.
- Canonical `V39-A` release in v72 is carried by canonical
  `external_contribution_alignment_packet@1`, canonical
  `module_conformance_report@1`, and canonical
  `v39a_external_contribution_alignment_evidence@1`; those artifacts remain bound to
  the frozen imported-single-PR subject kind, external-single-PR evaluation lane,
  explicit reference fixture id, three-layer scope model, default-negative precedent
  law, local-subject-only canonicalization, pinned policy provenance, and preserved
  separation between code alignment and meta-sequence alignment.
- The first accepted v72 reference remains intentionally bounded:
  the poetry utility contribution associated with PR `#293` is normalized as an
  imported internal-only utility contribution, not as a newly shipped API, URM, or web
  surface.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `137b148e51a6590f46af0e7fc85053f64473b34e`
- arc-completion CI runs:
  - PR `#294`
    - head commit: `68bf427c499733176288aa0eeb3134ce3716da1d`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23383729663`
    - conclusion: `success`
  - branch push before merge
    - head commit: `68bf427c499733176288aa0eeb3134ce3716da1d`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23383729219`
    - conclusion: `success`
  - merge push on `main`
    - merge commit: `137b148e51a6590f46af0e7fc85053f64473b34e`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23383945487`
    - conclusion: `success`
- merged implementation PRs:
  - `#294` (`Implement v72 external contribution alignment baseline`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v72_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v72_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v72_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v72/evidence_inputs/metric_key_continuity_assertion_v72.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v72/evidence_inputs/runtime_observability_comparison_v72.json`
  - external-alignment evidence input:
    `artifacts/agent_harness/v72/evidence_inputs/v39a_external_contribution_alignment_evidence_v72.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root:
    `artifacts/agent_harness/v72/runtime/evidence/codex/copilot/v72-closeout-main-1/`
  - parent-session raw/event streams:
    `artifacts/agent_harness/v72/runtime/evidence/codex/copilot/v72-closeout-main-1/`
  - the committed runtime stream remains provenance-only continuity evidence for the
    unchanged runtime lane; gate-relevant truth in v72 remains carried by the typed
    packet/report/evidence artifacts plus the closeout quality and stop-gate bundle.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS72_EDGES.md`

## Exit-Criteria Check (vNext+72)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V39-A` merged with green CI | required | `pass` | PR `#294`, merge commit `137b148e51a6590f46af0e7fc85053f64473b34e`, Actions runs `23383729663` and `23383945487` |
| New ADEU core schemas validate and export cleanly | required | `pass` | `packages/adeu_core_ir/schema/external_contribution_alignment_packet.v1.json`, `packages/adeu_core_ir/schema/module_conformance_report.v1.json`, mirrored `spec/` schemas, and `packages/adeu_core_ir/tests/test_ux_governance_export_schema.py` |
| One imported reference contribution materializes into a valid canonical packet | required | `pass` | `apps/api/fixtures/external_contribution_alignment/vnext_plus72/external_contribution_alignment_packet_pr293_poetry_utility.json` validates as `external_contribution_alignment_packet@1` |
| Canonical packet deterministically produces the canonical report | required | `pass` | `packages/adeu_core_ir/tests/test_external_contribution_alignment.py` and `module_conformance_report_pr293_poetry_utility.json` |
| Canonical evidence pins exact policy paths, policy hashes, and evaluator version | required | `pass` | `artifacts/agent_harness/v72/evidence_inputs/v39a_external_contribution_alignment_evidence_v72.json` |
| Code alignment and meta-sequence alignment remain separate reported dimensions | required | `pass` | `module_conformance_report_pr293_poetry_utility.json` exposes separate judgments and the evidence file sets `code_and_meta_sequence_dimensions_separated = true` |
| Claimed scope, observed surfaces, and accepted shipped scope remain separate | required | `pass` | `external_contribution_alignment_packet_pr293_poetry_utility.json` and `v39a_external_contribution_alignment_evidence_v72.json` |
| Precedent defaults negative unless explicitly granted | required | `pass` | `v39a_external_contribution_alignment_evidence_v72.json` sets `default_negative_precedent_verified = true` |
| Canonical subject is a committed local bundle, not live GitHub state | required | `pass` | `v39a_external_contribution_alignment_evidence_v72.json` sets `live_github_dependency_absent = true` and binds only local fixture paths |
| Missing required alignment inputs fail closed | required | `pass` | `packages/adeu_core_ir/tests/test_external_contribution_alignment_evidence.py` |
| Temp-repo replay honors pinned policy provenance | required | `pass` | `packages/adeu_core_ir/tests/test_external_contribution_alignment.py::test_derivation_honors_repository_root_for_pinned_policy_sources` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v72_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v72/evidence_inputs/metric_key_continuity_assertion_v72.json` records exact keyset equality versus v70 |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v72/evidence_inputs/runtime_observability_comparison_v72.json` |

## Stop-Gate Summary

```json
{
  "schema": "v72_closeout_stop_gate_summary@1",
  "arc": "vNext+72",
  "target_path": "V39-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v70": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 105,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v70_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v72_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+70","baseline_elapsed_ms":105,"baseline_source":"artifacts/stop_gate/report_v70_closeout.md","current_arc":"vNext+72","current_elapsed_ms":105,"current_source":"artifacts/stop_gate/report_v72_closeout.md","delta_ms":0,"notes":"v72 closeout keeps the frozen stop-gate schema family and metric keyset unchanged while adding the bounded V39-A external-contribution alignment lane.","schema":"runtime_observability_comparison@1"}
```

## V39A External Contribution Alignment Evidence

```json
{
  "code_and_meta_sequence_dimensions_separated": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md#v39a_external_contribution_alignment_contract@1",
  "default_negative_precedent_verified": true,
  "evaluator_id": "adeu_core_ir.external_contribution_alignment.derive_v39a_module_conformance@1",
  "evaluator_version": "1",
  "evidence_input_path": "artifacts/agent_harness/v72/evidence_inputs/v39a_external_contribution_alignment_evidence_v72.json",
  "external_contribution_alignment_packet_reference_hash": "e51a86598bf5778dbf53b4deb7bb24cbea9046702ef6e4a635e31a3b225f2274",
  "external_contribution_alignment_packet_reference_path": "apps/api/fixtures/external_contribution_alignment/vnext_plus72/external_contribution_alignment_packet_pr293_poetry_utility.json",
  "live_github_dependency_absent": true,
  "localized_subject_inputs_verified": true,
  "module_conformance_report_reference_hash": "32784d5f604cfc0cb7213792aad4a94faf14f685dc5844661f62b7c6fdbfb7d5",
  "module_conformance_report_reference_path": "apps/api/fixtures/external_contribution_alignment/vnext_plus72/module_conformance_report_pr293_poetry_utility.json",
  "notes": "v72 evidence pins the localized subject bundle, packet/report hash binding, policy provenance, and default-negative precedent semantics for the first retrospective external-alignment reference.",
  "policy_sources": [
    {
      "path": "AGENTS.md",
      "sha256": "4ee9bbb70d02036e72deaaba7348a3b7e8d93b0a7431535a4597be08b7af7f93"
    },
    {
      "path": "docs/DRAFT_EXTERNAL_CONTRIBUTION_ALIGNMENT_v0.md",
      "sha256": "6649fff0865205b383a8e7c30080599556a017723d0c902131742befae838d84"
    },
    {
      "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS72.md",
      "sha256": "a04bd709f89e1e9c5f13252664d2b6af7c5b6cdff2ddd20012bea595406bf8b6"
    }
  ],
  "schema": "v39a_external_contribution_alignment_evidence@1",
  "three_layer_scope_model_verified": true,
  "verification_passed": true
}
```

## Recommendation (Post v72)

- gate decision:
  - `V39A_EXTERNAL_CONTRIBUTION_ALIGNMENT_COMPLETE_ON_MAIN`
- rationale:
  - v72 closes the bounded `V39-A` baseline with canonical
    `external_contribution_alignment_packet@1`, canonical
    `module_conformance_report@1`, and canonical
    `v39a_external_contribution_alignment_evidence@1` integrated on `main`.
  - the reference subject remains explicitly local and retrospective; imported history
    is not rewritten as if it had native ADEU provenance.
  - no stop-gate schema-family, metric-key, or runtime-observability regressions were
    introduced by the lane.
  - the retrospective alignment lane is now typed and deterministic, but it remains
    explicitly bounded to one imported single-PR reference rather than a generalized
    all-module conformance engine.
