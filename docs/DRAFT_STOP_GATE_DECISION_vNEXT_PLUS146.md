# Draft Stop-Gate Decision (Post vNext+146)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS146.md`

Status: draft decision note (post-closeout capture, April 7, 2026 UTC).

Authority layer: closeout evidence on `arc/v54-r5` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS146.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v146_closeout_stop_gate_decision_on_arc_v54_r5",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+146` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS146.md`.
- This note captures bounded `V54-C` advisory O/E/D/U reconstruction release evidence
  only on `arc/v54-r5`; it does not by itself authorize workspace artifacts, API, UI,
  runtime, retrieval, or broader corpus-ingestion widening.
- Canonical `V54-C` release in `v146` is carried by the shipped
  `packages/adeu_history_semantics` package surface, authoritative and mirrored schema
  export for the three new downstream contracts, deterministic `v54c` fixtures/tests,
  and the canonical `v54c_history_reconstruction_evidence@1` evidence input under
  `artifacts/agent_harness/v146/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` now marks `V54-C`
  closed on `arc/v54-r5` and selects `V54-D` / `vNext+148` as the branch-local next
  path if the family continues.

## Evidence Source

- merged implementation PR:
  - `#367` (`feat(v146): add history ODEU reconstruction artifacts`)
- arc-completion merge commit:
  - `e8ba14a0906ee245b5ba048821c44d74c876eadf`
- merged-at timestamp:
  - `2026-04-07T17:55:02Z`
- implementation commits integrated by the merge:
  - `b950f850fff1440ccd98480076ef24a0207f31f6` (`feat(v146): add history ODEU reconstruction artifacts`)
  - `0dde681b2cbf7b04a92d2559c29eb8243ad4a8d2` (`fix(v146): address reconstruction review feedback`)
- targeted local verification actually run on the implementation branch and rerun in
  review fixing:
  - `PYTHONPATH=packages/adeu_history_semantics/src .venv/bin/python -m adeu_history_semantics.export_schema`
  - `.venv/bin/ruff check packages/adeu_history_semantics`
  - `PYTHONPATH=packages/adeu_history_semantics/src .venv/bin/pytest packages/adeu_history_semantics/tests`
  - focused review-fix rerun:
    - `PYTHONPATH=packages/adeu_history_semantics/src:packages/adeu_ir/src .venv/bin/python -m pytest packages/adeu_history_semantics/tests/test_history_semantics_v54c.py -q`
    - result: `13 passed`
- targeted verification results captured in committed branch-local evidence:
  - `artifacts/meta_loop/V54/V54-C/integration/implementation_verification.md`
  - `export_schema`: `pass`
  - `ruff`: `pass`
  - `pytest`: `34 passed`
- full-gate note:
  - `make check` was attempted before PR opening and rerun after review fixes
  - both runs remained red in the same shared dedicated-worktree baseline cluster:
    - `46 failed, 2190 passed, 6 skipped`
  - dominant remaining failures stayed in repo-wide `apps/api` worktree-root
    assumptions and existing `adeu_repo_description` baseline failures, not in the
    released `V54-C` package lane
- process correction:
  - PR `#367` was mistakenly opened as draft
  - Codex review was therefore manually triggered
  - the PR was later corrected to full review state before merge
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- docs-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=146`
- intentionally not run locally for this closeout step:
  - full `make check`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v146_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v146_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v146_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v146/evidence_inputs/metric_key_continuity_assertion_v146.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v146/evidence_inputs/runtime_observability_comparison_v146.json`
  - `V54-C` release evidence input:
    `artifacts/agent_harness/v146/evidence_inputs/v54c_history_reconstruction_evidence_v146.json`
  - committed runtime event stream:
    `artifacts/agent_harness/v146/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS146_EDGES.md`

## Exit-Criteria Check (vNext+146)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V54-C` merged on `arc/v54-r5` | required | `pass` | PR `#367`, merge commit `e8ba14a0906ee245b5ba048821c44d74c876eadf` |
| `packages/adeu_history_semantics` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_history_semantics` only |
| Three downstream contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_history_evidence_ref@1`, `adeu_history_odeu_lane_reconstruction@1`, and `adeu_history_odeu_reconstruction_packet@1` |
| Released `V54-A` and `V54-B` law remains inherited rather than reopened | required | `pass` | shipped `V54-C` compiles from released source, preclassification, ledger, slice, and theme surfaces only |
| Evidence refs remain grounded to released ledger-entry identity and exact entry text | required | `pass` | review hardening preserves original explicit-lane excerpt text and reject coverage enforces entry grounding |
| Absent or underdetermined lanes remain explicit rather than synthesized into full symmetry | required | `pass` | shipped reconstruction keeps absent/underdetermined lanes explicit and forbids synthesized evidence refs there |
| Advisory-only posture remains frozen | required | `pass` | released packet posture stays `advisory_overlay_only`; no warrant, winner, or workspace language was released |
| `reintegrated_summary` remains deferred | required | `pass` | shipped packet surface omits `reintegrated_summary` and tests reject it in `V54-C` |
| Workspace synthesis remains deferred | required | `pass` | shipped slice adds no workspace question, theme-frame, or snapshot contracts |
| Review hardening stayed bounded while strengthening correctness | required | `pass` | `0dde681` removed redundant evidence-ref revalidation, normalized join/scan behavior, and preserved exact explicit-lane excerpts without widening the slice |
| Targeted local package checks passed before merge | required | `pass` | PR branch evidence reports passing export-schema, `ruff`, and `pytest` with `34 passed`, then focused review-fix rerun with `13 passed` |
| Full local Python lane is not overclaimed | required | `pass` | closeout evidence records attempted `make check` failures truthfully, cites green PR CI, and does not claim a local passing `make check` result |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v146_closeout.json` with `schema = stop_gate_metrics@1`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v146/evidence_inputs/metric_key_continuity_assertion_v146.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v146/evidence_inputs/runtime_observability_comparison_v146.json` |

## Stop-Gate Summary

```json
{
  "schema": "v146_closeout_stop_gate_summary@1",
  "arc": "vNext+146",
  "target_path": "V54-C",
  "branch": "arc/v54-r5",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v144": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v144_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v146_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+144","current_arc":"vNext+146","baseline_source":"artifacts/stop_gate/report_v144_closeout.md","current_source":"artifacts/stop_gate/report_v146_closeout.md","baseline_elapsed_ms":134,"current_elapsed_ms":134,"delta_ms":0,"notes":"v146 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V54-C advisory O/E/D/U reconstruction lane on arc/v54-r5: one repo-owned adeu_history_semantics package only, three released downstream contracts over closed V54-A and V54-B surfaces, exact entry-grounded evidence refs, explicit absent or underdetermined lane posture, advisory-only packet identity, deterministic authoritative schema export plus root mirrors, deterministic v54c fixtures/tests, bounded review hardening for exact explicit-lane excerpt preservation, and no workspace, API, UI, runtime, or broader corpus-ingestion widening."}
```

## V54C History Reconstruction Evidence

```json
{"schema":"v54c_history_reconstruction_evidence@1","evidence_input_path":"artifacts/agent_harness/v146/evidence_inputs/v54c_history_reconstruction_evidence_v146.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS146.md#v146-continuation-contract-machine-checkable","merged_pr":"#367","merge_commit":"e8ba14a0906ee245b5ba048821c44d74c876eadf","implementation_commit":"b950f850fff1440ccd98480076ef24a0207f31f6","review_hardening_commit":"0dde681b2cbf7b04a92d2559c29eb8243ad4a8d2","implementation_packages":["adeu_history_semantics"],"released_upstream_schema_ids":["adeu_history_source_artifact@1","adeu_history_text_shape_signals@1","adeu_history_preclassification@1","adeu_history_ledger_entry@1","adeu_history_ledger@1","adeu_history_slice@1","adeu_history_theme_anchor@1"],"released_schema_ids":["adeu_history_evidence_ref@1","adeu_history_odeu_lane_reconstruction@1","adeu_history_odeu_reconstruction_packet@1"],"metric_key_continuity_assertion_path":"artifacts/agent_harness/v146/evidence_inputs/metric_key_continuity_assertion_v146.json","runtime_observability_comparison_path":"artifacts/agent_harness/v146/evidence_inputs/runtime_observability_comparison_v146.json","runtime_event_stream_path":"artifacts/agent_harness/v146/runtime/evidence/local/urm_events.ndjson","notes":"v146 evidence pins the released V54-C advisory reconstruction seam on arc/v54-r5: one repo-owned adeu_history_semantics package only, three released downstream contracts over closed V54-A and V54-B surfaces, exact entry-grounded evidence refs, deterministic advisory O/E/D/U packet identity, explicit absent or underdetermined lane posture, deterministic authoritative schema export plus root mirrors, deterministic v54c fixtures/tests, bounded review hardening for exact explicit-lane excerpt preservation, and no workspace, API, UI, runtime, or broader corpus-ingestion widening."}
```

## Recommendation (Post v146)

- gate decision:
  - `V54C_HISTORY_ODEU_RECONSTRUCTION_COMPLETE_ON_ARC_V54_R5`
- rationale:
  - `v146` closes the bounded advisory O/E/D/U reconstruction seam on `arc/v54-r5`
    after the released `V54-A` source/preclassification and released `V54-B`
    ledger/slice/theme substrate.
  - the shipped slice stayed properly bounded:
    - one repo-owned package
    - three released downstream contracts only
    - inherited `V54-A` and `V54-B` authority only
    - exact entry-grounded evidence refs only
    - one canonical O/E/D/U lane set per packet
    - explicit absent or underdetermined lane posture
    - advisory-only packet identity
    - no workspace synthesis
    - no API/UI/runtime widening
  - review hardening stayed bounded and materially improved provenance discipline:
    `0dde681` preserves original explicit-lane excerpts while tightening reconstruction
    behavior.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat versus the `v144` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` should now be read with `V54-C` closed on
    `arc/v54-r5` and `V54-D` / `vNext+148` selected as the next branch-local path if
    the family continues.
