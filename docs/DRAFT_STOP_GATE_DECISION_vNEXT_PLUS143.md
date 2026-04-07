# Draft Stop-Gate Decision (Post vNext+143)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md`

Status: draft decision note (post-merge closeout capture, April 7, 2026 UTC).

Authority layer: closeout evidence on `arc/v53-r4` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS143.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v143_closeout_stop_gate_decision_on_arc_v53_r4",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+143` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md`.
- This note captures bounded `V53-B` adjudication-lane evidence only on
  `arc/v53-r4`; it does not by itself authorize family-to-`main` integration,
  cumulative revision/register release, or direct `V45-D` test-intent
  integration.
- Canonical `V53-B` release in `v143` is carried by the shipped
  `packages/adeu_edge_ledger` package surface, authoritative and mirrored
  adjudication schema export, deterministic `v53b` fixtures/tests, and the
  canonical `v53b_edge_adjudication_evidence@1` evidence input under
  `artifacts/agent_harness/v143/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md` now marks `V53-B`
  closed on `arc/v53-r4` and advances the branch-local default next path to `V53-C`
  / `vNext+145`; it does not by itself authorize `V53-C` implementation.

## Evidence Source

- CI workflow: `ci` on PR `#366` against `arc/v53-r4`
- merged implementation PRs:
  - `#366` (`feat(v143): add edge adjudication ledger`)
- arc-completion merge commit on `arc/v53-r4`:
  - `e3d80e488831b0e2c672cc8c404f5c84cbbf0a3d`
- merged-at timestamp:
  - `2026-04-07T09:54:30Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- local verification posture reported before merge:
  - attempted `make check` on the PR branch initially failed on then-pre-existing
    import-order issues in:
    - `apps/api/tests/test_closeout_consistency_lint.py`
    - `apps/api/tests/test_semantic_compiler_closeout_lint.py`
  - targeted slice checks passed:
    - `PYTHONPATH=packages/adeu_edge_ledger/src:packages/adeu_symbol_audit/src:packages/adeu_repo_description/src:packages/adeu_ir/src .venv/bin/python -m ruff check packages/adeu_edge_ledger`
    - `PYTHONPATH=packages/adeu_edge_ledger/src:packages/adeu_symbol_audit/src:packages/adeu_repo_description/src:packages/adeu_ir/src .venv/bin/python -m pytest packages/adeu_edge_ledger/tests -q`
    - result: `21 passed`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v143_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v143_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v143_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v143/evidence_inputs/metric_key_continuity_assertion_v143.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v143/evidence_inputs/runtime_observability_comparison_v143.json`
  - `V53-B` release evidence input:
    `artifacts/agent_harness/v143/evidence_inputs/v53b_edge_adjudication_evidence_v143.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS143_EDGES.md`

## Exit-Criteria Check (vNext+143)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V53-B` merged with green CI on the family trunk | required | `pass` | PR `#366`, merge commit `e3d80e488831b0e2c672cc8c404f5c84cbbf0a3d`, checks `python/web/lean-formal = pass` |
| `packages/adeu_edge_ledger` remains the only active implementation package for the slice | required | `pass` | merged diff kept live implementation ownership under `packages/adeu_edge_ledger` only |
| One adjudication-ledger contract exports and mirrors deterministically | required | `pass` | package-local schema plus root mirror for `adeu_symbol_edge_adjudication_ledger@1` |
| Released `V53-A` catalog/probe/applicability bindings are consumed without reopening upstream law | required | `pass` | shipped adjudication helper binds to one released applicability frame and preserves catalog/probe/symbol identity fields from that frame |
| Adjudication rows retain full released frame coverage in released order | required | `pass` | shipped binding validation requires every frame row exactly once in frame order, and the committed reference fixture exercises the full row set |
| Contradictory, out-of-frame, and `not_applicable` override inputs fail closed | required | `pass` | shipped derivation helper and tests reject contradictory override input, unknown override refs, and explicit overrides against `not_applicable` rows |
| `underdetermined` rows remain bounded to carry-forward or explicit deferral only | required | `pass` | shipped helper emits `underdetermined` with no explicit evidence and `deferred` with a frozen deferral reason when explicit evidence is supplied |
| Support-field identity/order law is mechanized and auditable | required | `pass` | shipped models and tests preserve ordered `witness_ref` carry-through, ordered checked-no-witness edge refs, and reject contradictory support-field combinations |
| Revision/register and direct test-intent widening remain deferred | required | `pass` | shipped `V53-B` surface adds no cumulative revision/register artifacts and no direct `V45-D` joins |
| Review hardening stayed bounded while strengthening correctness and repo hygiene | required | `pass` | `2ae752a` hardened contradictory deferred-support rejection in models/tests, and `8dffc32` repaired branch-baseline import ordering in existing closeout-lint tests without widening `V53-B` semantics |
| Targeted local package checks passed before merge | required | `pass` | PR `#366` reported passing targeted `ruff` and `pytest` over `packages/adeu_edge_ledger/tests` with `21 passed` |
| Full local Python lane is not overclaimed | required | `pass` | closeout evidence records the attempted pre-merge `make check` failure truthfully, cites green PR CI, and does not claim a local passing `make check` result |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v143_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v143/evidence_inputs/metric_key_continuity_assertion_v143.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v143/evidence_inputs/runtime_observability_comparison_v143.json` |

## Stop-Gate Summary

```json
{
  "schema": "v143_closeout_stop_gate_summary@1",
  "arc": "vNext+143",
  "target_path": "V53-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v141": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 98,
  "runtime_observability_delta_ms": -36
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v141_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v143_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+141","current_arc":"vNext+143","baseline_source":"artifacts/stop_gate/report_v141_closeout.md","current_source":"artifacts/stop_gate/report_v143_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":98,"delta_ms":-36,"notes":"v143 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V53-B edge adjudication lane on arc/v53-r4: one repo-owned adeu_edge_ledger package only, one released adeu_symbol_edge_adjudication_ledger@1 contract over the released V53-A frame, full-catalog row coverage in released order, fail-closed contradictory/out-of-frame/not_applicable override rejection, underdetermined rows that defer rather than promote on explicit evidence, deterministic authoritative schema export plus root mirror, deterministic v53b fixtures/tests, bounded review hardening for contradictory deferred supports, and no cumulative revision/register or direct test-intent integration."}
```

## V53B Edge Adjudication Evidence

```json
{"schema":"v53b_edge_adjudication_evidence@1","evidence_input_path":"artifacts/agent_harness/v143/evidence_inputs/v53b_edge_adjudication_evidence_v143.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md#v143-continuation-contract-machine-checkable","merged_pr":"#366","merge_commit":"e3d80e488831b0e2c672cc8c404f5c84cbbf0a3d","implementation_commit":"153007bae76b815c5b560e5656dc3623e8eced9b","review_hardening_commit":"2ae752aa62f2881cf4433d2789fd70fb31ad4928","closeout_lint_alignment_commit":"8dffc32273d6df640c254041c33467149736cb3b","implementation_packages":["adeu_edge_ledger"],"starter_schema_ids":["adeu_symbol_edge_adjudication_ledger@1"],"edge_ledger_package_root":"packages/adeu_edge_ledger","edge_ledger_pyproject_path":"packages/adeu_edge_ledger/pyproject.toml","edge_ledger_package_init_source_path":"packages/adeu_edge_ledger/src/adeu_edge_ledger/__init__.py","edge_ledger_models_source_path":"packages/adeu_edge_ledger/src/adeu_edge_ledger/models.py","edge_ledger_adjudication_source_path":"packages/adeu_edge_ledger/src/adeu_edge_ledger/adjudication.py","edge_ledger_export_schema_source_path":"packages/adeu_edge_ledger/src/adeu_edge_ledger/export_schema.py","symbol_edge_adjudication_ledger_authoritative_schema_path":"packages/adeu_edge_ledger/schema/adeu_symbol_edge_adjudication_ledger.v1.json","symbol_edge_adjudication_ledger_mirror_schema_path":"spec/adeu_symbol_edge_adjudication_ledger.schema.json","reference_symbol_edge_adjudication_ledger_fixture_path":"packages/adeu_edge_ledger/tests/fixtures/v53b/reference_symbol_edge_adjudication_ledger.json","reject_contradictory_witness_input_fixture_path":"packages/adeu_edge_ledger/tests/fixtures/v53b/reject_contradictory_witness_input.json","test_adjudication_reference_path":"packages/adeu_edge_ledger/tests/test_edge_ledger_adjudication.py","test_export_schema_reference_path":"packages/adeu_edge_ledger/tests/test_edge_ledger_export_schema.py","worker_claim_baton_path":"artifacts/meta_loop/V53/V53-B/batons/005_arc_worker_implementation_claim.json","implementation_verification_doc_path":"artifacts/meta_loop/V53/V53-B/integration/implementation_verification.md","implementation_verification_baton_path":"artifacts/meta_loop/V53/V53-B/batons/006_meta_orchestrator_implementation_verification_ratification.json","adjudication_status_vocabulary":["not_applicable","applicable_unchecked","witness_found","checked_no_witness_found","underdetermined","deferred"],"explicit_override_channels":["witness_summaries","checked_no_witness_edge_class_refs"],"targeted_local_checks_only":true,"full_local_python_gate_not_claimed":true,"make_check_attempted_before_merge":true,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v143/evidence_inputs/metric_key_continuity_assertion_v143.json","runtime_observability_comparison_path":"artifacts/agent_harness/v143/evidence_inputs/runtime_observability_comparison_v143.json","runtime_event_stream_path":"artifacts/agent_harness/v143/runtime/evidence/local/urm_events.ndjson","notes":"v143 evidence pins the released V53-B edge adjudication seam on arc/v53-r4: one repo-owned adeu_edge_ledger package only, one released adeu_symbol_edge_adjudication_ledger@1 contract over the released V53-A frame, deterministic authoritative schema export plus root mirror, deterministic v53b fixtures/tests, full-catalog row coverage in released frame order, explicit fail-closed contradictory/out-of-frame/not_applicable override rejection, underdetermined rows bounded to carry-forward or explicit deferral only, support-ref identity/order preserved through stable witness and checked-no-witness channels, and no cumulative revision/register or direct test-intent widening."}
```

## Recommendation (Post v143)

- gate decision:
  - `V53B_EDGE_ADJUDICATION_COMPLETE_ON_ARC_V53_R4`
- rationale:
  - `v143` closes the bounded adjudication-hardening seam on `arc/v53-r4` before
    the revision and test-intent ladders widen.
  - the shipped slice stayed narrow and evidence-law-first:
    - one repo-owned package
    - one released adjudication ledger contract only
    - exact downstream `V53-A` consumption only
    - one exact fail-closed override law
    - one explicit witness / checked-no-witness support law
    - underdetermined rows deferred rather than promoted
    - no cumulative revision register
    - no direct test-intent integration
  - review hardening stayed bounded and materially improved correctness and closeout
    hygiene:
    - `2ae752a` forbids contradictory deferred support combinations
    - `8dffc32` repaired branch-baseline import ordering in existing closeout-lint
      tests without widening `V53-B`
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained informational-only and moved by `-36 ms` versus the
    `v141` baseline on the regenerated closeout bundle.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md` should now be read with `V53-B` closed on
    `arc/v53-r4` and `V53-C` / `vNext+145` selected as the next branch-local default
    path.
