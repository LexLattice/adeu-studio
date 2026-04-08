# Draft Stop-Gate Decision (Post vNext+144)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md`

Status: draft decision note (post-hoc closeout capture, April 7, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS144.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v144_family_branch_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+144` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md`.
- This note captures bounded `V54-B` ledger / slice / theme release evidence only; it
  does not authorize evidence refs, O/E/D/U packets, workspace artifacts, API, UI,
  runtime, or broader corpus-ingestion widening by itself.
- Canonical `V54-B` release in `v144` is carried by the shipped
  `packages/adeu_history_semantics` package surface, authoritative and mirrored schema
  export for the four new downstream contracts, deterministic `v54b` fixtures/tests,
  and the canonical `v54b_history_semantics_evidence@1` evidence input under
  `artifacts/agent_harness/v144/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` now marks `V54-B`
  closed on `arc/v54-r4` and selects `V54-C` / `vNext+146` as the branch-local next
  path if the family continues.

## Evidence Source

- merged implementation PR:
  - `#365` (`feat(v144): add history ledger and theme anchors`)
- arc-completion merge commit: `490416ad472f6e9f4476fef995929502c4afbbaa`
- merged-at timestamp: `2026-04-07T09:54:30Z`
- implementation commits integrated by the merge:
  - `5e8b44fd65c2f137604f5498d7dd31df3bea8a21` (`feat(v144): add history ledger and theme anchors`)
  - `cdfb7fdb5ab3b469611707146306aedbf2cb7172` (`fix(v144): harden theme anchor aggregation`)
  - `5f9c9301df8d4ab8f8c11553cfeb9a023cec58e3` (`fix(testing): sort api closeout lint imports`)
- targeted local verification actually run on the implementation branch and rerun in
  meta-loop ratification:
  - `PYTHONPATH=packages/adeu_history_semantics/src:packages/adeu_ir/src .venv/bin/python -m ruff check packages/adeu_history_semantics`
  - `PYTHONPATH=packages/adeu_history_semantics/src:packages/adeu_ir/src .venv/bin/python -m pytest packages/adeu_history_semantics/tests -q`
- targeted verification results captured in committed branch-local evidence:
  - `artifacts/meta_loop/V54/V54-B/integration/implementation_verification.md`
  - `ruff`: `pass`
  - `pytest`: `21 passed`
- docs-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=144`
- intentionally not run locally for this closeout step:
  - full `make check`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v144_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v144_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v144_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v144/evidence_inputs/metric_key_continuity_assertion_v144.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v144/evidence_inputs/runtime_observability_comparison_v144.json`
  - `V54-B` release evidence input:
    `artifacts/agent_harness/v144/evidence_inputs/v54b_history_semantics_evidence_v144.json`
  - committed runtime event stream:
    `artifacts/agent_harness/v144/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS144_EDGES.md`

## Exit-Criteria Check (vNext+144)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V54-B` merged on `arc/v54-r4` | required | `pass` | PR `#365`, merge commit `490416ad472f6e9f4476fef995929502c4afbbaa` |
| `packages/adeu_history_semantics` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_history_semantics` only |
| Four downstream contracts export and mirror deterministically | required | `pass` | package-local schemas plus root mirrors for `adeu_history_ledger_entry@1`, `adeu_history_ledger@1`, `adeu_history_slice@1`, and `adeu_history_theme_anchor@1` |
| `V54-A` authority and source-domain law remains inherited rather than reopened | required | `pass` | shipped `V54-B` path still compiles from released source artifact plus preclassification only, and shorthand alias widening remains rejected |
| One preclassification to one ledger-entry law is retained with no same-speaker collapse | required | `pass` | `test_consecutive_same_speaker_chronology_does_not_merge_entries` keeps four preclassifications and four ledger entries with preserved chronology |
| Slice grouping remains deterministic and chronology-local | required | `pass` | shipped slices are still maximal contiguous same-role runs over released `order_index` and are pinned by `reference_history_projection.json` |
| Theme-anchor derivation stays descriptive, deterministic, and fail-closed | required | `pass` | released theme-key/theme-label/supporting-term derivation is fixture-pinned, `reject_no_lawful_theme_terms.txt` fails closed, and `cdfb7fdb5ab3b469611707146306aedbf2cb7172` hardens duplicate anchor-entry rejection |
| Quoted or fenced multiline content does not mint new roles or entries | required | `pass` | `test_quoted_or_fenced_multiline_content_stays_inside_one_entry` keeps quoted and fenced content inside one released entry and one released slice |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v144_closeout.json` with `schema = stop_gate_metrics@1`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v144/evidence_inputs/metric_key_continuity_assertion_v144.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v144/evidence_inputs/runtime_observability_comparison_v144.json` |

## Stop-Gate Summary

```json
{
  "schema": "v144_closeout_stop_gate_summary@1",
  "arc": "vNext+144",
  "target_path": "V54-B",
  "branch": "arc/v54-r4",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v142": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 134,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v142_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v144_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+142",
  "current_arc": "vNext+144",
  "baseline_source": "artifacts/stop_gate/report_v142_closeout.md",
  "current_source": "artifacts/stop_gate/report_v144_closeout.md",
  "baseline_elapsed_ms": 134,
  "current_elapsed_ms": 134,
  "delta_ms": 0,
  "notes": "v144 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V54-B history-semantics ledger/slice/theme substrate on arc/v54-r4: one repo-owned adeu_history_semantics package only, four new bounded downstream contracts over released V54-A source and preclassification surfaces, one preclassification to one ledger-entry law, maximal contiguous same-role slice grouping, deterministic theme-term/theme-label/theme-key/supporting-term derivation with fail-closed no-term rejection, deterministic schema mirrors and v54b fixtures, and no evidence-ref O/E/D/U workspace API UI runtime or broader corpus-ingestion widening."
}
```

## V54B History Semantics Evidence

```json
{
  "schema": "v54b_history_semantics_evidence@1",
  "evidence_input_path": "artifacts/agent_harness/v144/evidence_inputs/v54b_history_semantics_evidence_v144.json",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS144.md#v144-continuation-contract-machine-checkable",
  "merged_pr": "#365",
  "merge_commit": "490416ad472f6e9f4476fef995929502c4afbbaa",
  "implementation_commit": "5e8b44fd65c2f137604f5498d7dd31df3bea8a21",
  "review_hardening_commit": "cdfb7fdb5ab3b469611707146306aedbf2cb7172",
  "closeout_lint_hygiene_commit": "5f9c9301df8d4ab8f8c11553cfeb9a023cec58e3",
  "implementation_packages": [
    "adeu_history_semantics"
  ],
  "upstream_released_schema_ids": [
    "adeu_history_source_artifact@1",
    "adeu_history_text_shape_signals@1",
    "adeu_history_preclassification@1"
  ],
  "released_schema_ids": [
    "adeu_history_ledger_entry@1",
    "adeu_history_ledger@1",
    "adeu_history_slice@1",
    "adeu_history_theme_anchor@1"
  ],
  "metric_key_continuity_assertion_path": "artifacts/agent_harness/v144/evidence_inputs/metric_key_continuity_assertion_v144.json",
  "runtime_observability_comparison_path": "artifacts/agent_harness/v144/evidence_inputs/runtime_observability_comparison_v144.json",
  "runtime_event_stream_path": "artifacts/agent_harness/v144/runtime/evidence/local/urm_events.ndjson",
  "notes": "v144 evidence pins the released V54-B history-semantics ledger/slice/theme substrate on arc/v54-r4: one repo-owned adeu_history_semantics package only, four bounded downstream contracts over released V54-A source and preclassification surfaces, one preclassification to one ledger-entry law, maximal contiguous same-role slices, deterministic theme-anchor grouping by identical derived theme_key only, fail-closed no-lawful-theme-term rejection, deterministic schema mirrors and v54b fixtures, and no evidence-ref O/E/D/U workspace API UI runtime or broader corpus-ingestion widening."
}
```

## Recommendation (Post v144)

- gate decision:
  - `V54B_HISTORY_LEDGER_SLICE_THEME_COMPLETE_ON_ARC_V54_R4`
- rationale:
  - `v144` closes the deterministic ledger / slice / theme substrate slice on
    `arc/v54-r4` after the family was selected and narrowed in
    `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` plus the `V54` support mapping docs.
  - the shipped slice stayed properly bounded:
    - one repo-owned package
    - four released downstream contracts only
    - inherited `V54-A` authority and source-domain law only
    - one preclassification to one ledger-entry law only
    - one maximal contiguous same-role slice grouping law only
    - one deterministic descriptive theme-anchor law only
    - one fail-closed no-lawful-theme-term posture only
    - no evidence ref
    - no O/E/D/U
    - no workspace
    - no API/UI/runtime widening
    - no broader corpus-ingestion claim
  - review hardening stayed bounded and materially improved provenance discipline:
    `cdfb7fdb5ab3b469611707146306aedbf2cb7172` hardens theme-anchor aggregation by
    rejecting duplicate anchor entry membership without widening the released contract
    surface.
  - the follow-on shared-test import-order cleanup
    `5f9c9301df8d4ab8f8c11553cfeb9a023cec58e3` is branch hygiene only and does not
    widen `V54-B` semantics.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained flat at `0 ms` delta versus the `v142` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v37.md` should now be read with `V54-B` closed on
    `arc/v54-r4` and `V54-C` / `vNext+146` selected as the next branch-local path if
    the family continues.
