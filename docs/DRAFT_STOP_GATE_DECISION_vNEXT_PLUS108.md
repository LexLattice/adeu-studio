# Draft Stop-Gate Decision (Post vNext+108)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS108.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v108_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+108` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md`.
- This note captures bounded `V47-C` coexistence/adoption evidence only; it does not
  authorize repo-wide migration, imported selector/predicate ownership transition,
  execution posture, approval posture, waiver issuance, deferral issuance, or current
  markdown supersession by itself.
- Canonical `V47-C` release in v108 is carried by the shipped
  `adeu_semantic_source` / `adeu_commitments_ir` source, model, schema-export, and
  deterministic fixture surfaces plus the canonical
  `v47c_authoritative_normative_markdown_coexistence_evidence@1` evidence input under
  `artifacts/agent_harness/v108/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#330` (`V47-C: add ANM coexistence profile`)
- arc-completion merge commit: `a2adfb4d94692cd7e3a041ed57df4a5266a8a56a`
- merged-at timestamp: `2026-04-01T22:28:13Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v108_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v108_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v108_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v108/evidence_inputs/metric_key_continuity_assertion_v108.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v108/evidence_inputs/runtime_observability_comparison_v108.json`
  - `V47-C` release evidence input:
    `artifacts/agent_harness/v108/evidence_inputs/v47c_authoritative_normative_markdown_coexistence_evidence_v108.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v108/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS108_EDGES.md`

## Exit-Criteria Check (vNext+108)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V47-C` merged with green CI | required | `pass` | PR `#330`, merge commit `a2adfb4d94692cd7e3a041ed57df4a5266a8a56a`, checks `python/web/lean-formal = pass` |
| Released coexistence profile ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_commitments_ir/schema/anm_markdown_coexistence_profile.v1.json`, `spec/anm_markdown_coexistence_profile.schema.json`, and parity coverage in `packages/adeu_commitments_ir/tests/test_export_schema.py` |
| Standalone vs companion classification is deterministic over one declared snapshot and bounded source scope | required | `pass` | `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py` and deterministic replay in `packages/adeu_semantic_source/tests/test_anm_coexistence.py::test_v47c_reference_profile_replays_deterministically` |
| Every companion example preserves explicit non-override posture and explicit embedding/linkage semantics | required | `pass` | `packages/adeu_semantic_source/tests/fixtures/v47c/reference_coexistence_spec.json`, committed profile fixture `packages/adeu_commitments_ir/tests/fixtures/v47c/reference_anm_markdown_coexistence_profile.json`, and source-row validation in `AnmCoexistenceSourceRow` |
| Supersession fields remain exact and non-contradictory | required | `pass` | builder/model validation in `anm.py` and `anm_models.py`, plus tests `test_v47c_rejects_inconsistent_supersession_spec` and `test_v47c_rejects_inconsistent_supersession_fields` |
| Host/companion linkage fails closed on missing, stale, source-scope incompatible, or authority-contradictory references | required | `pass` | reject specs `reject_orphaned_host_spec.json`, `reject_stale_or_contradictory_host_spec.json`, and tests `test_v47c_rejects_orphaned_host_linkage`, `test_v47c_rejects_stale_or_contradictory_host_linkage`, and `test_v47c_rejects_contradictory_host_authority_kind` |
| Migration discipline remains explicit, bounded, and non-migratory | required | `pass` | `MigrationDiscipline` surface in `anm_models.py`, builder enforcement in `anm.py`, and test `test_v47c_rejects_source_row_posture_forbidden_by_migration_discipline` |
| Adoption-boundary rows use the same frozen action vocabulary as source rows | required | `pass` | `AllowedConstrainAction` typing, exported coexistence profile schema, and tests `test_v47c_rejects_boundary_action_drift_spec` and `test_v47c_rejects_boundary_action_outside_frozen_vocabulary` |
| Malformed coexistence compile inputs fail closed through `AnmCompileError` instead of leaking raw key errors | required | `pass` | compile-input normalization helpers in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py` and `test_v47c_wraps_malformed_source_row_specs_in_anm_compile_error` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v108_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v108/evidence_inputs/metric_key_continuity_assertion_v108.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v108/evidence_inputs/runtime_observability_comparison_v108.json` |

## Stop-Gate Summary

```json
{
  "schema": "v108_closeout_stop_gate_summary@1",
  "arc": "vNext+108",
  "target_path": "V47-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v107": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 111,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v107_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v108_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+107","current_arc":"vNext+108","baseline_source":"artifacts/stop_gate/report_v107_closeout.md","current_source":"artifacts/stop_gate/report_v108_closeout.md","baseline_elapsed_ms":111,"current_elapsed_ms":111,"delta_ms":0,"notes":"v108 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V47-C coexistence/adoption lane: deterministic standalone-vs-companion classification, explicit non-override and embedding posture, bounded migration discipline, explicit adoption-boundary rows, fail-closed host/companion linkage validation, and retained authoritative/mirrored schema export parity."}
```

## V47C Authoritative Normative Markdown Coexistence Evidence

```json
{"schema":"v47c_authoritative_normative_markdown_coexistence_evidence@1","evidence_input_path":"artifacts/agent_harness/v108/evidence_inputs/v47c_authoritative_normative_markdown_coexistence_evidence_v108.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md#v108-continuation-contract-machine-checkable","merged_pr":"#330","merge_commit":"a2adfb4d94692cd7e3a041ed57df4a5266a8a56a","implementation_packages":["adeu_semantic_source","adeu_commitments_ir"],"coexistence_profile_implementation_source_path":"packages/adeu_semantic_source/src/adeu_semantic_source/anm.py","coexistence_profile_model_source_path":"packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py","coexistence_profile_authoritative_schema_path":"packages/adeu_commitments_ir/schema/anm_markdown_coexistence_profile.v1.json","coexistence_profile_mirror_schema_path":"spec/anm_markdown_coexistence_profile.schema.json","test_reference_paths":["packages/adeu_semantic_source/tests/test_anm_coexistence.py","packages/adeu_commitments_ir/tests/test_anm_coexistence_profile.py","packages/adeu_commitments_ir/tests/test_export_schema.py"],"accepted_standalone_source_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/standalone_policy.adeu.md","accepted_companion_source_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/companion_policy.md","accepted_current_authority_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/current_authority.md","accepted_reference_spec_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/reference_coexistence_spec.json","accepted_profile_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47c/reference_anm_markdown_coexistence_profile.json","rejected_inconsistent_supersession_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/reject_inconsistent_supersession_spec.json","rejected_orphaned_host_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/reject_orphaned_host_spec.json","rejected_stale_or_contradictory_host_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/reject_stale_or_contradictory_host_spec.json","rejected_boundary_action_drift_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47c/reject_boundary_action_drift_spec.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v108/evidence_inputs/metric_key_continuity_assertion_v108.json","runtime_observability_comparison_path":"artifacts/agent_harness/v108/evidence_inputs/runtime_observability_comparison_v108.json","runtime_event_stream_path":"artifacts/agent_harness/v108/runtime/evidence/local/urm_events.ndjson","notes":"v108 evidence pins the released V47-C coexistence/adoption baseline on main: one canonical anm_markdown_coexistence_profile@1, deterministic standalone-versus-companion classification, exact supersession-field consistency, explicit embedding posture, fail-closed host/companion linkage validation, bounded migration discipline, explicit adoption-boundary action matrix, and retained non-executive/non-migratory authority posture."}
```

## Recommendation (Post v108)

- gate decision:
  - `V47C_AUTHORITATIVE_NORMATIVE_MARKDOWN_COEXISTENCE_COMPLETE_ON_MAIN`
- rationale:
  - v108 closes the bounded `V47-C` coexistence/adoption seam on `main` by taking the
    released `V47-A` + `V47-B` ANM stack and making its standalone-vs-companion,
    non-override, embedding, migration, and adoption-boundary posture explicit.
  - the shipped slice is doctrine-first and non-executive: it does not reopen ANM
    source syntax, normalized `D-IR`, bootstrap predicate contracts, checker facts,
    result-set grammar, ledger semantics, ownership transition, or execution authority.
  - companion posture now has explicit host linkage, explicit embedding posture, exact
    supersession-field consistency, and fail-closed rejection of orphaned, stale,
    incompatible, or authority-contradictory references.
  - migration posture is bounded and informative only; it does not authorize repo-wide
    markdown conversion or automatic authority transfer.
  - adoption-boundary rows now make the released ANM stack’s allowed constrain actions,
    later-lock-required actions, and forbidden actions explicit in one typed profile.
  - authoritative schema, mirrored export, committed fixtures, and targeted tests stay
    in parity for the released coexistence surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v107 baseline).
  - later `V47` work, if selected, should now move to selector/predicate ownership
    transition on top of the closed `V47-A` + `V47-B` + `V47-C` stack.
