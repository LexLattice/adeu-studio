# Draft Stop-Gate Decision (Post vNext+142)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`

Status: draft decision note (post-hoc closeout capture, April 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS142.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v142_family_branch_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+142` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md`.
- This note captures bounded `V54-A` history-semantics evidence only; it does not
  authorize ledger, slice, theme, O/E/D/U, workspace, API, UI, runtime, or broader
  corpus-ingestion widening by itself.
- Canonical `V54-A` release in `v142` is carried by the shipped
  `packages/adeu_history_semantics` package surface, authoritative and mirrored starter
  schema export, deterministic `v54a` fixtures/tests, and the canonical
  `v54a_history_semantics_evidence@1` evidence input under
  `artifacts/agent_harness/v142/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` now marks `V54-A`
  closed on `arc/v54-r3` and selects `V54-B` / `vNext+144` as the branch-local next
  path if the family continues.

## Evidence Source

- CI workflow: `ci` on PR `#364`
- merged implementation PRs:
  - `#364` (`feat(v142): implement V54-A history semantics starter`)
- arc-completion merge commit: `54c3933d0e4b9dac77cfa97ffa4130b1bb473426`
- merged-at timestamp: `2026-04-06T23:13:40Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- targeted local verification actually run on the implementation PR branch:
  - `PYTHONPATH=packages/adeu_history_semantics/src .venv/bin/python -m ruff check packages/adeu_history_semantics`
  - `PYTHONPATH=packages/adeu_history_semantics/src .venv/bin/python -m pytest packages/adeu_history_semantics/tests -q`
- intentionally not run locally for this slice:
  - full `make check`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v142_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v142_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v142_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v142/evidence_inputs/metric_key_continuity_assertion_v142.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v142/evidence_inputs/runtime_observability_comparison_v142.json`
  - `V54-A` release evidence input:
    `artifacts/agent_harness/v142/evidence_inputs/v54a_history_semantics_evidence_v142.json`
  - committed runtime event stream:
    `artifacts/agent_harness/v142/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS142_EDGES.md`

## Exit-Criteria Check (vNext+142)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V54-A` merged with green CI | required | `pass` | PR `#364`, merge commit `54c3933d0e4b9dac77cfa97ffa4130b1bb473426`, checks `python/web/lean-formal = pass` |
| `packages/adeu_history_semantics` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_history_semantics` only |
| Three starter source-authority contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_history_source_artifact@1`, `adeu_history_text_shape_signals@1`, and `adeu_history_preclassification@1` |
| Starter authority root remains normalized source text after line-ending normalization only | required | `pass` | shipped source artifact and tests keep raw-byte authority out of scope and bind identity only to `input_kind` plus normalized `source_text_hash` |
| Starter source domain remains bounded to explicit role-header `conversation_history` with one exact timestamp prefix law | required | `pass` | shipped helper admits only full `User:` / `Assistant:` / `System:` headers and one optional bracketed `YYYY-MM-DD HH:MM` prefix immediately before the full role header |
| Whole-source fail-closed posture retained | required | `pass` | shipped reject fixtures cover shorthand aliases, unheadered sources, malformed timestamp placement, mixed-domain malformed blocks, and widened-surface attempts |
| Projection-only metadata does not mint source identity | required | `pass` | shipped source identity binds only to `input_kind` and normalized `source_text_hash`; label/wave/notes remain projection-only and are covered by tests |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v142_closeout.json` with `schema = stop_gate_metrics@1`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v142/evidence_inputs/metric_key_continuity_assertion_v142.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v142/evidence_inputs/runtime_observability_comparison_v142.json` |

## Stop-Gate Summary

```json
{
  "schema": "v142_closeout_stop_gate_summary@1",
  "arc": "vNext+142",
  "target_path": "V54-A",
  "branch": "arc/v54-r3",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v140": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v140_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v142_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+140","current_arc":"vNext+142","baseline_source":"artifacts/stop_gate/report_v140_closeout.md","current_source":"artifacts/stop_gate/report_v142_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":134,"delta_ms":0,"notes":"v142 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V54-A history-semantics starter on arc/v54-r3: one repo-owned adeu_history_semantics package only, three new bounded source-authority contracts, normalized source text after line-ending normalization as the sole authority root, one explicit-role-header conversation_history starter domain only, one exact optional bracketed timestamp prefix form only, projection-only source metadata outside identity law, deterministic schema mirrors and v54a fixtures, and no ledger slice theme O/E/D/U workspace API UI runtime or broader corpus-ingestion widening."}
```

## V54A History Semantics Evidence

```json
{"schema":"v54a_history_semantics_evidence@1","evidence_input_path":"artifacts/agent_harness/v142/evidence_inputs/v54a_history_semantics_evidence_v142.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS142.md#v142-continuation-contract-machine-checkable","merged_pr":"#364","merge_commit":"54c3933d0e4b9dac77cfa97ffa4130b1bb473426","implementation_commit":"95f26b72310d8a9844097ea6bb0a19560098cde7","review_hardening_commit":"00c44494d3fcdb17543a1115f7ad92554ef9b2e2","implementation_packages":["adeu_history_semantics"],"starter_schema_ids":["adeu_history_source_artifact@1","adeu_history_text_shape_signals@1","adeu_history_preclassification@1"],"starter_source_domain":"conversation_history_with_explicit_role_headers","starter_source_authority_semantics":"normalized_source_text_authoritative_after_line_ending_normalization","starter_timestamp_prefix_format":"optional_bracketed_yyyy_mm_dd_hh_mm_immediately_before_full_role_header_only","test_reference_paths":["packages/adeu_history_semantics/tests/test_history_semantics_v54a.py","packages/adeu_history_semantics/tests/test_history_semantics_export_schema.py"],"metric_key_continuity_assertion_path":"artifacts/agent_harness/v142/evidence_inputs/metric_key_continuity_assertion_v142.json","runtime_observability_comparison_path":"artifacts/agent_harness/v142/evidence_inputs/runtime_observability_comparison_v142.json","notes":"v142 evidence pins the released V54-A history-semantics starter on arc/v54-r3: one repo-owned adeu_history_semantics package only, three bounded source-authority contracts, normalized source text after line-ending normalization as the only authority root, one explicit-role-header conversation_history starter domain, one exact optional bracketed timestamp prefix form, deterministic text-shape and preclassification overlays, projection-only source metadata outside identity law, deterministic schema mirrors and v54a fixtures, and no ledger slice theme O/E/D/U workspace API UI runtime or broader corpus-ingestion widening."}
```

## Recommendation (Post v142)

- gate decision:
  - `V54A_HISTORY_SEMANTICS_STARTER_COMPLETE_ON_ARC_V54_R3`
- rationale:
  - `v142` closes the source-authority and export substrate slice on `arc/v54-r3`
    after the family was selected and narrowed in `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md`
    plus the `V54` support mapping docs.
  - the shipped slice stayed properly bounded:
    - one repo-owned package
    - three released source contracts only
    - one normalized-text authority root only
    - one explicit-role-header `conversation_history` domain only
    - one exact optional bracketed timestamp prefix form only
    - one whole-source fail-closed posture only
    - one deterministic text-shape / preclassification overlay only
    - no ledger
    - no slice
    - no theme
    - no O/E/D/U
    - no workspace
    - no API/UI/runtime widening
    - no broader corpus-ingestion claim
  - review hardening stayed bounded and materially improved repo alignment:
    `00c44494d3fcdb17543a1115f7ad92554ef9b2e2` narrowed timestamp lookalike rejection,
    shared role-to-origin mapping through one constant, and strengthened CRLF
    normalization evidence without widening the starter domain.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat at `0 ms` delta versus the `v140` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` should now be read with `V54-A` closed on
    `arc/v54-r3` and `V54-B` / `vNext+144` selected as the next branch-local path if
    the family continues.
