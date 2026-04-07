# Draft Stop-Gate Decision (Post vNext+145)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS145.md`

Status: draft decision note (post-closeout capture, April 7, 2026 UTC).

Authority layer: closeout evidence on `arc/v53-r5` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS145.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v145_closeout_stop_gate_decision_on_arc_v53_r5",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+145` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS145.md`.
- This note captures bounded `V53-C` revision-register release evidence only on
  `arc/v53-r5`; it does not by itself authorize family-to-`main` integration,
  direct `V45-D` probe/test-intent joins, live taxonomy mutation, or broader reviewer
  / enforcement widening.
- Canonical `V53-C` release in `v145` is carried by the shipped
  `packages/adeu_edge_ledger` package surface, authoritative and mirrored
  `adeu_edge_taxonomy_revision_register@1` schema export, deterministic `v53c`
  fixtures/tests, and the canonical `v53c_edge_revision_register_evidence@1` evidence
  input under `artifacts/agent_harness/v145/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md` now marks `V53-C`
  closed on `arc/v53-r5` and advances the branch-local default next path to `V53-D`
  / `vNext+147`; it does not by itself authorize `V53-D` implementation.

## Evidence Source

- CI workflow: `ci` on PR `#368` against `arc/v53-r5`
- merged implementation PRs:
  - `#368` (`feat(v145): add edge taxonomy revision register`)
- arc-completion merge commit on `arc/v53-r5`:
  - `dbb5b03eb207f43f051d673a9aa41cf0b06291e0`
- merged-at timestamp:
  - `2026-04-07T17:55:02Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- local verification posture reported before and after review fix:
  - targeted slice checks passed:
    - `PYTHONPATH=packages/adeu_edge_ledger/src:packages/adeu_symbol_audit/src:packages/adeu_repo_description/src:packages/adeu_ir/src .venv/bin/python -m ruff check packages/adeu_edge_ledger`
    - `PYTHONPATH=packages/adeu_edge_ledger/src:packages/adeu_symbol_audit/src:packages/adeu_repo_description/src:packages/adeu_ir/src .venv/bin/python -m pytest packages/adeu_edge_ledger/tests -q`
    - result before PR open: `34 passed`
    - result after review-fix rerun on touched lane:
      `packages/adeu_edge_ledger/tests/test_edge_ledger_revision.py -q`
      -> `14 passed`
  - `make check` was attempted before PR open and rerun after review fixes
  - both full-gate runs remained red in the same shared dedicated-worktree baseline
    cluster:
    - `46 failed, 2190 passed, 6 skipped`
  - dominant remaining failures stayed in repo-wide `apps/api` worktree-root
    assumptions and existing `adeu_repo_description` baseline failures, not in the
    released `V53-C` package lane
- process correction:
  - PR `#368` was mistakenly opened as draft
  - Codex review was therefore manually triggered
  - the PR was later corrected to full review state before merge
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v145_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v145_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v145_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v145/evidence_inputs/metric_key_continuity_assertion_v145.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v145/evidence_inputs/runtime_observability_comparison_v145.json`
  - `V53-C` release evidence input:
    `artifacts/agent_harness/v145/evidence_inputs/v53c_edge_revision_register_evidence_v145.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS145_EDGES.md`

## Exit-Criteria Check (vNext+145)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V53-C` merged with green CI on the family trunk | required | `pass` | PR `#368`, merge commit `dbb5b03eb207f43f051d673a9aa41cf0b06291e0`, checks `python/web/lean-formal = pass` |
| `packages/adeu_edge_ledger` remains the only active implementation package for the slice | required | `pass` | merged diff kept live implementation ownership under `packages/adeu_edge_ledger` only |
| One revision-register contract exports and mirrors deterministically | required | `pass` | package-local schema plus root mirror for `adeu_edge_taxonomy_revision_register@1` |
| Released `V53-A` and released `V53-B` remain consumed, not reopened | required | `pass` | shipped register binds released catalog/probe/applicability and one bound released adjudication ledger without reopening upstream law |
| Append-only same-lineage register law is mechanized and auditable | required | `pass` | shipped register model and fixtures preserve stable append order, exact same-ledger append, and fail closed on cross-ledger append |
| Decision-shape, candidate-ref, and lineage-parent law fail closed | required | `pass` | shipped validators and reject fixtures cover invalid decision shape, inadmissible candidate refs, unknown parent refs, and lineage cycles |
| Revision support stays anchored to admitted `V53-B` rows | required | `pass` | shipped register entries require admitted supporting adjudication row refs and reject deferred-only support posture |
| Live taxonomy mutation and direct `V45-D` integration remain deferred | required | `pass` | shipped `V53-C` surface adds no automatic catalog rewrite helpers and no direct test-intent joins |
| Review hardening stayed bounded while strengthening correctness | required | `pass` | `36a191a` hardened unexpected `revision_decision` rejection and added focused regression coverage without widening the slice |
| Targeted local package checks passed before merge | required | `pass` | PR branch evidence reports passing targeted `ruff` plus `pytest` with `34 passed`, then focused review-fix rerun with `14 passed` |
| Full local Python lane is not overclaimed | required | `pass` | closeout evidence records both attempted `make check` failures truthfully, cites green PR CI, and does not claim a local passing `make check` result |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v145_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v145/evidence_inputs/metric_key_continuity_assertion_v145.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v145/evidence_inputs/runtime_observability_comparison_v145.json` |

## Stop-Gate Summary

```json
{
  "schema": "v145_closeout_stop_gate_summary@1",
  "arc": "vNext+145",
  "target_path": "V53-C",
  "branch": "arc/v53-r5",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v143": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 98,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v143_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v145_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+143","current_arc":"vNext+145","baseline_source":"artifacts/stop_gate/report_v143_closeout.md","current_source":"artifacts/stop_gate/report_v145_closeout.md","baseline_elapsed_ms":98,"current_elapsed_ms":98,"delta_ms":0,"notes":"v145 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V53-C edge revision-register lane on arc/v53-r5: one repo-owned adeu_edge_ledger package only, one released adeu_edge_taxonomy_revision_register@1 contract over released V53-A and V53-B surfaces, append-only same-ledger lineage, fail-closed decision-shape and lineage-parent law, bounded edge_class candidate refs with no subject overlap, deterministic authoritative schema export plus root mirror, deterministic v53c fixtures/tests, bounded review hardening for unexpected revision_decision rejection, and no live taxonomy mutation or direct V45-D test-intent integration."}
```

## V53C Edge Revision Register Evidence

```json
{"schema":"v53c_edge_revision_register_evidence@1","evidence_input_path":"artifacts/agent_harness/v145/evidence_inputs/v53c_edge_revision_register_evidence_v145.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS145.md#v145-continuation-contract-machine-checkable","merged_pr":"#368","merge_commit":"dbb5b03eb207f43f051d673a9aa41cf0b06291e0","implementation_commit":"46288afee05925aa487858358de4aae44c231d42","review_hardening_commit":"36a191a9b01c873a7f7def4606dd869593f690f0","implementation_packages":["adeu_edge_ledger"],"released_upstream_schema_ids":["adeu_edge_class_catalog@1","adeu_edge_probe_template_catalog@1","adeu_symbol_edge_applicability_frame@1","adeu_symbol_edge_adjudication_ledger@1"],"released_schema_ids":["adeu_edge_taxonomy_revision_register@1"],"metric_key_continuity_assertion_path":"artifacts/agent_harness/v145/evidence_inputs/metric_key_continuity_assertion_v145.json","runtime_observability_comparison_path":"artifacts/agent_harness/v145/evidence_inputs/runtime_observability_comparison_v145.json","runtime_event_stream_path":"artifacts/agent_harness/v145/runtime/evidence/local/urm_events.ndjson","notes":"v145 evidence pins the released V53-C edge revision-register seam on arc/v53-r5: one repo-owned adeu_edge_ledger package only, one released adeu_edge_taxonomy_revision_register@1 contract over released V53-A and V53-B surfaces, append-only same-ledger lineage, deterministic authoritative schema export plus root mirror, deterministic v53c fixtures/tests, fail-closed decision-shape, candidate-ref, parent-ref, cross-ledger append, and deferred-only-support rejection, bounded review hardening for unexpected revision_decision rejection, and no live taxonomy mutation or direct test-intent widening."}
```

## Recommendation (Post v145)

- gate decision:
  - `V53C_EDGE_REVISION_REGISTER_COMPLETE_ON_ARC_V53_R5`
- rationale:
  - `v145` closes the bounded cumulative revision-register seam on `arc/v53-r5`
    after the released `V53-A` taxonomy/applicability and released `V53-B`
    adjudication substrate.
  - the shipped slice stayed narrow and evidence-law-first:
    - one repo-owned package
    - one released revision-register contract only
    - exact downstream `V53-A` and `V53-B` consumption only
    - one exact append-only same-ledger lineage law
    - one exact decision-shape law
    - one exact candidate-ref admissibility / non-overlap law
    - one exact adjudication-support anchor law
    - no live taxonomy mutation
    - no direct `V45-D` test-intent integration
  - review hardening stayed bounded and materially improved correctness:
    - `36a191a` rejects unexpected `revision_decision` values fail closed
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability remained informational-only and stayed flat versus the
    `v143` baseline.
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v36.md` should now be read with `V53-C` closed on
    `arc/v53-r5` and `V53-D` / `vNext+147` selected as the next branch-local default
    path.
