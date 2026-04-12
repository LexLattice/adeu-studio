# Draft Stop-Gate Decision (Post vNext+149)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS149.md`

Status: draft decision note (post-closeout capture, April 12, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS149.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v149_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+149` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS149.md`.
- This note captures bounded `V55-A` constitutional coherence starter evidence only on
  `main`; it does not by itself authorize `V55-B`, `V55-C`, repo-wide gating,
  autonomous prose-native reasoning, multi-descendant rollout, descendant runtime or
  product surfaces, or support-doc promotion into released family law.
- Canonical `V55-A` shipment in `v149` is carried by the shipped
  `packages/adeu_constitutional_coherence` package surface, the thin
  `apps/api/scripts/lint_constitutional_coherence_v55a.py` seam, authoritative and
  mirrored record-shape schema export, deterministic `v55a` admissions/report/register
  fixtures, and the canonical `v55a_constitutional_coherence_starter_evidence@1`
  evidence input under `artifacts/agent_harness/v149/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- merged implementation PR:
  - `#375` (`[codex] Add V55-A constitutional coherence starter`)
- arc-completion merge commit:
  - `48c27957dc74c04a1b445204b3211a77ac8ded48`
- merged-at timestamp:
  - `2026-04-12T22:33:33+03:00`
- implementation commits integrated by the merge:
  - `bd52338cb9aee98f48ddf6aa891b83ac3799a072`
    (`Add V55-A constitutional coherence starter`)
  - `0ef5dd679009bc266b3738d0f4c25cc59b3dcaa2`
    (`Tighten V55-A checker review fixes`)
- targeted local verification actually run on the implementation branch and rerun in
  review hardening:
  - `.venv/bin/python -m pytest -q packages/adeu_constitutional_coherence/tests`
  - `.venv/bin/python -m pytest -q packages/adeu_constitutional_coherence/tests apps/api/tests/test_lint_constitutional_coherence_v55a.py`
- full local Python lane actually run before merge:
  - `make check`
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=149`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v149_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v149_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v149_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v149/evidence_inputs/metric_key_continuity_assertion_v149.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v149/evidence_inputs/runtime_observability_comparison_v149.json`
  - `V55-A` starter evidence input:
    `artifacts/agent_harness/v149/evidence_inputs/v55a_constitutional_coherence_starter_evidence_v149.json`
  - committed runtime event stream witness:
    `artifacts/agent_harness/v149/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS149_EDGES.md`

## Exit-Criteria Check (vNext+149)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V55-A` merged on `main` | required | `pass` | PR `#375`, merge commit `48c27957dc74c04a1b445204b3211a77ac8ded48` |
| `packages/adeu_constitutional_coherence` remains the only active implementation package for the slice | required | `pass` | merged diff limited live implementation ownership to `packages/adeu_constitutional_coherence` only |
| One thin script seam exists and stays bounded to the warning-only checker lane | required | `pass` | shipped CLI surface is `apps/api/scripts/lint_constitutional_coherence_v55a.py` only |
| Four canonical record-shape schemas export and mirror deterministically | required | `pass` | authoritative and mirrored schema pairs exist for `constitutional_support_admission_record@1`, `constitutional_coherence_report@1`, `constitutional_unresolved_seam_register@1`, and `constitutional_coherence_lane_drift_record@1` |
| Exact six-artifact admitted seed set remains closed and canonicalized | required | `pass` | committed admissions fixture plus review hardening enforce missing/extra admission rejection and canonical ordering |
| Checker remains warning-only and non-gating | required | `pass` | CLI returns `0`, emits warnings and unresolved seams, and review suggestions to gate on warnings were intentionally not taken |
| Structured-input-only contract remains the sole checker execution path | required | `pass` | checker consumes admissions, explicit headers, explicit JSON blocks, explicit refs, and explicit witness refs only |
| Malformed designated structured blocks fail closed without turning malformed prose into authority | required | `pass` | `test_malformed_designated_support_block_fails_closed` and `test_malformed_non_designated_block_is_ignored` cover the exact posture |
| Structurally unevaluable predicates emit unresolved seams instead of silent pass/fail | required | `pass` | reference unresolved seam register records `7` `not_evaluable_yet` entries for bounded deferred predicates |
| Descendant trial remains support-surface mode only over the crypto exemplar | required | `pass` | committed report fixture evaluates `docs/support/crypto data spec2.md` without minting runtime or release authority |
| Review hardening improved seed-set safety and path handling without widening scope | required | `pass` | `0ef5dd679009bc266b3738d0f4c25cc59b3dcaa2` added exact seed-set enforcement, path-safety guards, and unresolved `stderr` emission while preserving warning-only posture |
| Targeted local tests and full local Python lane passed before merge | required | `pass` | targeted package/CLI pytest runs passed and `make check` passed before merge |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v149_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v149/evidence_inputs/metric_key_continuity_assertion_v149.json` records exact keyset equality versus `v147` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v149/evidence_inputs/runtime_observability_comparison_v149.json` records `67 ms` current elapsed, `98 ms` baseline elapsed, `-31 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v149_closeout_stop_gate_summary@1",
  "arc": "vNext+149",
  "target_path": "V55-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v147": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 67,
  "runtime_observability_delta_ms": -31
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v147_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v149_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+147","current_arc":"vNext+149","baseline_source":"artifacts/stop_gate/report_v147_closeout.md","current_source":"artifacts/stop_gate/report_v149_closeout.md","baseline_elapsed_ms":98,"current_elapsed_ms":67,"delta_ms":-31,"notes":"v149 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V55-A constitutional coherence starter on main: one repo-owned adeu_constitutional_coherence package only, one thin warning-only CLI seam, four canonical record-shape schemas, one exact six-artifact admitted seed set, committed admissions/report/unresolved/drift fixtures, a support-surface-only descendant trial over docs/support/crypto data spec2.md, review hardening for exact seed-set enforcement and path safety, and no runtime/product or CI-gating widening."}
```

## V55A Constitutional Coherence Starter Evidence

```json
{"schema":"v55a_constitutional_coherence_starter_evidence@1","evidence_input_path":"artifacts/agent_harness/v149/evidence_inputs/v55a_constitutional_coherence_starter_evidence_v149.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS149.md#machine-checkable-contract","merged_pr":"#375","merge_commit":"48c27957dc74c04a1b445204b3211a77ac8ded48","implementation_commit":"bd52338cb9aee98f48ddf6aa891b83ac3799a072","review_hardening_commit":"0ef5dd679009bc266b3738d0f4c25cc59b3dcaa2","implementation_packages":["adeu_constitutional_coherence"],"starter_schema_ids":["constitutional_support_admission_record@1","constitutional_coherence_report@1","constitutional_unresolved_seam_register@1","constitutional_coherence_lane_drift_record@1"],"warning_only_checker_preserved":true,"support_surface_descendant_trial_only":true,"reference_warning_count":2,"reference_unresolved_entry_count":7,"reference_lane_drift_entry_count":3,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v149/evidence_inputs/metric_key_continuity_assertion_v149.json","runtime_observability_comparison_path":"artifacts/agent_harness/v149/evidence_inputs/runtime_observability_comparison_v149.json","runtime_event_stream_path":"artifacts/agent_harness/v149/runtime/evidence/local/urm_events.ndjson","notes":"v149 evidence pins the bounded V55-A constitutional coherence starter on main: one repo-owned adeu_constitutional_coherence package only, one thin warning-only CLI seam, four canonical record-shape schemas with authoritative and mirrored export, one exact six-artifact admitted seed set, deterministic admissions/report/unresolved/drift fixtures, exact seed-set enforcement and path-safety review hardening, a support-surface-only descendant trial over docs/support/crypto data spec2.md, and no V55-B/V55-C widening, autonomous prose-native reasoning, runtime/product surfaces, or CI-gating promotion."}
```

## Recommendation (Post v149)

- gate decision:
  - `V55A_CONSTITUTIONAL_COHERENCE_STARTER_COMPLETE_ON_MAIN`
- rationale:
  - `v149` closes the bounded `V55-A` starter seam on `main`.
  - the shipped slice stayed properly bounded:
    - one repo-owned package
    - one thin CLI seam
    - one warning-only checker
    - four canonical record-shape schemas
    - one exact admitted six-artifact seed set
    - one support-surface-only descendant trial
    - no runtime/product widening
    - no CI-gating promotion
    - no support-doc self-promotion into released family law
  - review hardening stayed bounded and materially improved correctness:
    `0ef5dd679009bc266b3738d0f4c25cc59b3dcaa2` tightened exact seed-set
    enforcement, repo-relative/path-safety checks, and unresolved register emission
    without widening the checker past the lock.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability improved by `31 ms` versus the `v147` baseline.
