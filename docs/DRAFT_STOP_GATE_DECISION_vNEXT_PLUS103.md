# Draft Stop-Gate Decision (Post vNext+103)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS103.md`

Status: draft decision note (post-hoc closeout capture, April 1, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS103.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v103_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+103` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS103.md`.
- This note captures bounded `V45-D` release evidence only; it does not authorize
  optimization-register release, descriptive-to-normative binding, scheduler
  automation, mutation entitlement, or recursive-governance widening.
- Canonical `V45-D` release in v103 is carried by the
  `packages/adeu_repo_description` test-intent-matrix schema/model/extraction
  surfaces, deterministic fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus103/`, and the canonical
  `v45d_repo_test_intent_matrix_evidence@1` evidence input under
  `artifacts/agent_harness/v103/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#325` (`V45-D: implement v103 repo test intent matrix`)
- arc-completion merge commit: `d54c9d8c8a224aa2161a060e00fa1ce002181e1c`
- merged-at timestamp: `2026-04-01T05:37:54Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v103_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v103_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v103_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v103/evidence_inputs/metric_key_continuity_assertion_v103.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v103/evidence_inputs/runtime_observability_comparison_v103.json`
  - `V45-D` release evidence input:
    `artifacts/agent_harness/v103/evidence_inputs/v45d_repo_test_intent_matrix_evidence_v103.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v103/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS103_EDGES.md`

## Exit-Criteria Check (vNext+103)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-D` merged with green CI | required | `pass` | PR `#325`, merge commit `d54c9d8c8a224aa2161a060e00fa1ce002181e1c`, checks `python/web/lean-formal = pass` |
| Canonical `repo_test_intent_matrix@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_test_intent_matrix.v1.json`, `spec/repo_test_intent_matrix.schema.json` |
| Deterministic replay over the accepted v103 fixture is stable | required | `pass` | replay check in `packages/adeu_repo_description/tests/test_repo_description_v45d.py` and accepted fixture `apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reference.json` |
| Explicit snapshot identity/hash, explicit test-source binding, and explicit `test_source_set_hash` are present | required | `pass` | accepted fixture replay plus required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Explicit `V45-B` binding is enforced against one symbol catalog and one dependency graph over the same snapshot/source posture | required | `pass` | `validate_repo_test_intent_matrix_against_v45b` in `packages/adeu_repo_description/src/adeu_repo_description/models.py` and pair validation coverage in `packages/adeu_repo_description/tests/test_repo_description_v45d.py` |
| Each emitted row preserves one test-claim/assertion unit with distinct guarded-surface, claimed-invariant, and observed-assertion fields | required | `pass` | row-model anchors in `models.py` and row-granularity assertions in `test_repo_description_v45d.py` |
| Internal guarded-surface refs resolve against the bound `V45-B` baseline and external/out-of-scope refs remain typed | required | `pass` | guarded-surface validation in `models.py`, accepted fixture replay, and reject fixture `repo_test_intent_matrix_v103_reject_guarded_surface_ref_without_boundary_typing.json` |
| `source_artifact_refs` membership is constrained to the declared `test_source_set` | required | `pass` | membership validation in `models.py` and reject fixture `repo_test_intent_matrix_v103_reject_source_artifact_ref_outside_test_source_set.json` |
| Unsupported claim shapes, mismatched `V45-B` binding, and authority laundering fail closed | required | `pass` | reject fixtures under `apps/api/fixtures/repo_description/vnext_plus103/` and rejection assertions in `test_repo_description_v45d.py` |
| Relative import aliases, annotation-only assignments, and mutually exclusive branch provenance are handled safely | required | `pass` | extractor hardening in `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and focused tests `test_v45d_accepts_annotation_only_annassign_in_test_body`, `test_v45d_resolves_relative_import_from_aliases_to_internal_module_boundaries`, and `test_v45d_branch_local_provenance_does_not_leak_between_if_branches` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v103_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v103/evidence_inputs/metric_key_continuity_assertion_v103.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v103/evidence_inputs/runtime_observability_comparison_v103.json` |

## Stop-Gate Summary

```json
{
  "schema": "v103_closeout_stop_gate_summary@1",
  "arc": "vNext+103",
  "target_path": "V45-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v102": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v102_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v103_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+102","current_arc":"vNext+103","baseline_source":"artifacts/stop_gate/report_v102_closeout.md","current_source":"artifacts/stop_gate/report_v103_closeout.md","baseline_elapsed_ms":96,"current_elapsed_ms":96,"delta_ms":0,"notes":"v103 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V45-D repo_test_intent_matrix@1 surface with explicit claimed-vs-observed row structure, bounded V45-B binding, relative-import alias resolution, annotation-only assignment handling, and branch-local provenance isolation guards."}
```

## V45D Repo Test Intent Matrix Evidence

```json
{"schema":"v45d_repo_test_intent_matrix_evidence@1","evidence_input_path":"artifacts/agent_harness/v103/evidence_inputs/v45d_repo_test_intent_matrix_evidence_v103.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS103.md#v103-continuation-contract-machine-checkable","merged_pr":"#325","merge_commit":"d54c9d8c8a224aa2161a060e00fa1ce002181e1c","repo_test_intent_matrix_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_test_intent_matrix.v1.json","repo_test_intent_matrix_mirror_schema_path":"spec/repo_test_intent_matrix.schema.json","accepted_test_intent_matrix_fixture_path":"apps/api/fixtures/repo_description/vnext_plus103/repo_test_intent_matrix_v103_reference.json"}
```

## Recommendation (Post v103)

- gate decision:
  - `V45D_REPO_TEST_INTENT_MATRIX_COMPLETE_ON_MAIN`
- rationale:
  - v103 closes the bounded `V45-D` widening seam on `main` by shipping a
    deterministic `repo_test_intent_matrix@1` surface with explicit test-source
    provenance, explicit claimed-vs-observed row structure, explicit bounded
    confidence/gating posture, and explicit binding back to the released `V45-B`
    symbol/dependency baseline.
  - review hardening closed concrete extractor correctness gaps around annotation-only
    assignments, relative import alias resolution, and branch-local provenance drift.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v102 baseline).
  - broader widening into `V45-E` and later lanes remains a planning selection beyond
    this decision note.
