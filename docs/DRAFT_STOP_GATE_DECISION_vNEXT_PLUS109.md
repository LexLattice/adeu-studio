# Draft Stop-Gate Decision (Post vNext+109)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS109.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v109_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+109` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md`.
- This note captures bounded `V47-D` ownership-transition evidence only; it does not
  authorize repo-wide markdown migration, downstream consumer binding, execution
  posture, approval posture, waiver issuance, deferral issuance, or current markdown
  supersession by itself.
- Canonical `V47-D` release in v109 is carried by the shipped
  `adeu_semantic_source` / `adeu_commitments_ir` source, model, schema-export, and
  deterministic fixture surfaces plus the canonical
  `v47d_authoritative_normative_markdown_selector_predicate_ownership_transition_evidence@1`
  evidence input under `artifacts/agent_harness/v109/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#331` (`V47-D: add ANM ownership transition profile`)
- arc-completion merge commit: `30624dbc63b9adce1aff7b35db779b90595c473b`
- merged-at timestamp: `2026-04-02T09:37:16Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v109_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v109_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v109_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v109/evidence_inputs/metric_key_continuity_assertion_v109.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v109/evidence_inputs/runtime_observability_comparison_v109.json`
  - `V47-D` release evidence input:
    `artifacts/agent_harness/v109/evidence_inputs/v47d_authoritative_normative_markdown_selector_predicate_ownership_transition_evidence_v109.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v109/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS109_EDGES.md`

## Exit-Criteria Check (vNext+109)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V47-D` merged with green CI | required | `pass` | PR `#331`, merge commit `30624dbc63b9adce1aff7b35db779b90595c473b`, checks `python/web/lean-formal = pass` |
| Released ownership profile ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_commitments_ir/schema/anm_selector_predicate_ownership_profile.v1.json`, `spec/anm_selector_predicate_ownership_profile.schema.json`, and parity coverage in `packages/adeu_commitments_ir/tests/test_export_schema.py` |
| Owner-layer vocabulary stays normalized to the released bootstrap term rather than introducing cross-slice drift | required | `pass` | `SelectorOwnershipOwnerLayer` / `PredicateOwnershipOwnerLayer` typing in `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`, accepted `v47d` profile fixture, and `test_v47d_vocabularies_are_exact` |
| Selector and predicate rows enforce explicit bootstrap/imported mutual-exclusion invariants | required | `pass` | model validation in `anm_models.py`, compile-time checks in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, and tests `test_v47d_rejects_selector_row_with_conflicting_bootstrap_and_imported_fields` and `test_v47d_rejects_implicit_selector_promotion` |
| Compatibility posture ships as an explicit four-combination matrix rather than prose alone | required | `pass` | `compatibility_rules` in `packages/adeu_commitments_ir/tests/fixtures/v47d/reference_anm_selector_predicate_ownership_profile.json`, model validation in `anm_models.py`, and tests `test_v47d_rejects_incomplete_compatibility_matrix` and `test_v47d_rejects_missing_present_compatibility_combination` |
| Contradictory mixed-ownership posture fails closed | required | `pass` | compile/model validation in `anm.py` and `anm_models.py`, plus tests `test_v47d_rejects_present_mixed_combination_marked_forbidden` and `test_v47d_rejects_allowed_row_with_forbidden_posture` |
| Imported owned refs resolve fail closed against declared snapshot, source scope, and identity/version binding | required | `pass` | imported-registry resolution in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, reject specs `reject_dangling_imported_selector_spec.json` and `reject_incompatible_imported_predicate_version_spec.json`, and tests `test_v47d_rejects_dangling_imported_selector_handle` and `test_v47d_rejects_incompatible_imported_predicate_version` |
| Pure-bootstrap released chains replay unchanged under `V47-D` with no silent reinterpretation into owned semantics | required | `pass` | accepted bootstrap-only spec `packages/adeu_semantic_source/tests/fixtures/v47d/bootstrap_only_ownership_spec.json`, deterministic replay in `test_v47d_bootstrap_only_profile_preserves_released_replay`, and frozen `bootstrap_only` matrix rows in the committed `v47d` profile fixture |
| Accepted mixed bootstrap/owned doctrine remains explicit and bounded | required | `pass` | accepted transition spec `packages/adeu_semantic_source/tests/fixtures/v47d/reference_ownership_spec.json`, committed profile fixture `packages/adeu_commitments_ir/tests/fixtures/v47d/reference_anm_selector_predicate_ownership_profile.json`, and deterministic replay in `test_v47d_reference_profile_replays_deterministically` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v109_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v109/evidence_inputs/metric_key_continuity_assertion_v109.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v109/evidence_inputs/runtime_observability_comparison_v109.json` |

## Stop-Gate Summary

```json
{
  "schema": "v109_closeout_stop_gate_summary@1",
  "arc": "vNext+109",
  "target_path": "V47-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v108": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 111,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v108_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v109_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+108","current_arc":"vNext+109","baseline_source":"artifacts/stop_gate/report_v108_closeout.md","current_source":"artifacts/stop_gate/report_v109_closeout.md","baseline_elapsed_ms":111,"current_elapsed_ms":111,"delta_ms":0,"notes":"v109 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V47-D ownership-transition lane: one canonical anm_selector_predicate_ownership_profile@1, normalized bootstrap owner-layer vocabulary, explicit selector/predicate row mutual-exclusion invariants, a typed four-combination compatibility matrix, fail-closed imported-ref resolution, and backward-compatible bootstrap replay without silent reinterpretation into owned semantics."}
```

## V47D Authoritative Normative Markdown Selector / Predicate Ownership Transition Evidence

```json
{"schema":"v47d_authoritative_normative_markdown_selector_predicate_ownership_transition_evidence@1","evidence_input_path":"artifacts/agent_harness/v109/evidence_inputs/v47d_authoritative_normative_markdown_selector_predicate_ownership_transition_evidence_v109.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md#v109-continuation-contract-machine-checkable","merged_pr":"#331","merge_commit":"30624dbc63b9adce1aff7b35db779b90595c473b","implementation_packages":["adeu_semantic_source","adeu_commitments_ir"],"ownership_profile_implementation_source_path":"packages/adeu_semantic_source/src/adeu_semantic_source/anm.py","ownership_profile_model_source_path":"packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py","ownership_profile_authoritative_schema_path":"packages/adeu_commitments_ir/schema/anm_selector_predicate_ownership_profile.v1.json","ownership_profile_mirror_schema_path":"spec/anm_selector_predicate_ownership_profile.schema.json","test_reference_paths":["packages/adeu_semantic_source/tests/test_anm_ownership_transition.py","packages/adeu_commitments_ir/tests/test_anm_selector_predicate_ownership_profile.py","packages/adeu_commitments_ir/tests/test_export_schema.py"],"accepted_bootstrap_only_spec_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47d/bootstrap_only_ownership_spec.json","accepted_transition_spec_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47d/reference_ownership_spec.json","accepted_profile_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47d/reference_anm_selector_predicate_ownership_profile.json","rejected_implicit_selector_promotion_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47d/reject_implicit_selector_promotion_spec.json","rejected_dangling_imported_selector_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47d/reject_dangling_imported_selector_spec.json","rejected_incompatible_imported_predicate_version_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47d/reject_incompatible_imported_predicate_version_spec.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v109/evidence_inputs/metric_key_continuity_assertion_v109.json","runtime_observability_comparison_path":"artifacts/agent_harness/v109/evidence_inputs/runtime_observability_comparison_v109.json","runtime_event_stream_path":"artifacts/agent_harness/v109/runtime/evidence/local/urm_events.ndjson","notes":"v109 evidence pins the released V47-D ownership-transition baseline on main: one canonical anm_selector_predicate_ownership_profile@1, normalized bootstrap owner-layer continuity across slices, explicit bootstrap-vs-owned selector/predicate rows, a typed four-combination compatibility matrix, fail-closed dangling or incompatible imported-ref resolution, contradictory mixed-ownership rejection, and retained non-executive/non-migratory authority posture."}
```

## Recommendation (Post v109)

- gate decision:
  - `V47D_AUTHORITATIVE_NORMATIVE_MARKDOWN_OWNERSHIP_TRANSITION_COMPLETE_ON_MAIN`
- rationale:
  - v109 closes the bounded `V47-D` ownership-transition seam on `main` by taking the
    released `V47-A` + `V47-B` + `V47-C` ANM stack and making bootstrap-vs-owned
    selector/predicate posture explicit in one typed profile.
  - the shipped slice is doctrine-first and non-executive: it does not reopen ANM
    source syntax, normalized `D-IR`, checker facts, result-set grammar, ledger
    semantics, coexistence/adoption doctrine, repo-wide migration, or downstream
    consumer binding.
  - selector and predicate rows now carry exact mutual-exclusion invariants, so
    bootstrap and imported ref carriers cannot coexist contradictorily inside one row.
  - compatibility posture is now machine-inspectable through one required
    four-combination matrix with explicit allowed/forbidden, replay, later-lock, and
    mixed-ownership-constrained fields.
  - imported selector handles and imported predicate-registry refs resolve fail closed
    against declared snapshot, source scope, identity, and version rather than being
    promoted by naming convention.
  - pure-bootstrap released chains continue to replay unchanged where retirement is not
    yet selected, and no silent reinterpretation into owned semantics is shipped.
  - authoritative schema, mirrored export, committed fixtures, and targeted tests stay
    in parity for the released ownership-transition surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v108 baseline).
  - later `V47` work, if selected, should now move to downstream policy-bearing
    consumer seams on top of the closed `V47-A` + `V47-B` + `V47-C` + `V47-D` stack.
