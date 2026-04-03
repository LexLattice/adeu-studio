# Draft Stop-Gate Decision (Post vNext+118)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS118.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS118.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v118_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+118` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS118.md`.
- This note captures bounded `V49-B` semantic recovery evidence only; it does not
  authorize deterministic lowering, `V48` bridge behavior, CLI/API/web consumers,
  multi-domain semantic expansion, or imported-bundle precedent by itself.
- Canonical `V49-B` release in `v118` is carried by the shipped
  `adeu_semantic_forms` parser source, committed deterministic `v49b` fixtures,
  parser/package tests, and the canonical
  `v49b_semantic_forms_recovery_evidence@1` evidence input under
  `artifacts/agent_harness/v118/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now marks `V49-B`
  closed on `main` and advances the branch-local default next path to `V49-C`; it
  does not select any later `V49` closeout by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#340` (`[codex] add semantic forms recovery parser`)
- arc-completion merge commit: `4d26a77f2962ee75d1eb92d912b9c18af2c61370`
- merged-at timestamp: `2026-04-03T23:08:50Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v118_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v118_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v118_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v118/evidence_inputs/metric_key_continuity_assertion_v118.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v118/evidence_inputs/runtime_observability_comparison_v118.json`
  - `V49-B` release evidence input:
    `artifacts/agent_harness/v118/evidence_inputs/v49b_semantic_forms_recovery_evidence_v118.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v118/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS118_EDGES.md`

## Exit-Criteria Check (vNext+118)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V49-B` merged with green CI | required | `pass` | PR `#340`, merge commit `4d26a77f2962ee75d1eb92d912b9c18af2c61370`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_semantic_forms` package remains the only live owner of the first recovery lane | required | `pass` | `packages/adeu_semantic_forms/pyproject.toml`, `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py`, and absence of prototype-tree import into live package paths |
| Recovery consumes one released `adeu_semantic_parse_profile@1` and emits one released `adeu_semantic_parse_result@1` only | required | `pass` | `parse_nl_to_semantic_result(...)` in `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py`, released models in `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and parser replay tests |
| Recovery remains bounded to `repo_policy_work` and released `V49-A` relation / lane / object vocabularies only | required | `pass` | parser profile usage plus reference fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49b/` |
| Parse-result outcome vocabulary remains frozen and fail-closed | required | `pass` | `resolved_singleton`, `typed_alternatives`, `clarification_required`, `rejected_unsupported` in parser outputs, committed fixtures, and parser tests |
| Candidate distinctness remains semantic-hash only and alternative ordering remains deterministic | required | `pass` | `_dedupe_candidates(...)`, semantic-hash ordering logic, and `test_typed_alternatives_are_sorted_by_semantic_hash` / `test_dedupe_candidates_collapses_same_semantic_hash` |
| Clarification remains zero-candidate only and unsupported inputs remain explicit reject posture | required | `pass` | parser outcome logic plus `reference_semantic_parse_result_clarification_required.json`, `reference_semantic_parse_result_rejected_unsupported.json`, and parser tests |
| Exact anchor / exact phrase precedence remains explicit and equal-strength conflicts do not silently choose | required | `pass` | precedence logic in `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py` and `reference_semantic_parse_result_exact_anchor_precedence.json` |
| Recovered `forbid_effect` cues preserve all matched effects instead of collapsing to one winner | required | `pass` | parser effect recovery plus `test_all_recovered_forbid_effects_are_preserved` |
| Recovery explanations remain projection/support-only and do not affect semantic identity | required | `pass` | parser emits released `V49-A` normal forms and support-only `evidence_summary`; candidate sameness remains `normal_form.semantic_hash` only |
| Deterministic `v49b` fixtures replay exactly | required | `pass` | `packages/adeu_semantic_forms/tests/test_semantic_forms_parser.py` and fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49b/` |
| No deterministic lowering, `V48` bridge helper, or product consumer ships in this slice | required | `pass` | implementation footprint limited to parser/package/tests/fixtures and absence of lowering/bridge/consumer files under `packages/adeu_semantic_forms` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v118_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v118/evidence_inputs/metric_key_continuity_assertion_v118.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v118/evidence_inputs/runtime_observability_comparison_v118.json` |

## Stop-Gate Summary

```json
{
  "schema": "v118_closeout_stop_gate_summary@1",
  "arc": "vNext+118",
  "target_path": "V49-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v117": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 107,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v117_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v118_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+117","current_arc":"vNext+118","baseline_source":"artifacts/stop_gate/report_v117_closeout.md","current_source":"artifacts/stop_gate/report_v118_closeout.md","baseline_elapsed_ms":107,"current_elapsed_ms":107,"delta_ms":0,"notes":"v118 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V49-B semantic recovery lane: one repo-owned adeu_semantic_forms parser, one released repo_policy_work parse profile, typed parse-result emission only through released V49-A contracts, semantic-hash candidate distinctness, deterministic alternative ordering, zero-candidate clarification posture, explicit exact-anchor precedence, preserved multi-effect forbid recovery, deterministic v49b replay fixtures, and no lowering, V48 bridge, or product-surface widening."}
```

## V49B Semantic Forms Recovery Evidence

```json
{"schema":"v49b_semantic_forms_recovery_evidence@1","evidence_input_path":"artifacts/agent_harness/v118/evidence_inputs/v49b_semantic_forms_recovery_evidence_v118.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS118.md#v118-continuation-contract-machine-checkable","merged_pr":"#340","merge_commit":"4d26a77f2962ee75d1eb92d912b9c18af2c61370","implementation_packages":["adeu_semantic_forms"],"semantic_forms_package_root":"packages/adeu_semantic_forms","semantic_forms_pyproject_path":"packages/adeu_semantic_forms/pyproject.toml","semantic_forms_models_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py","semantic_forms_parse_profile_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py","semantic_forms_parser_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py","semantic_forms_package_init_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py","test_reference_paths":["packages/adeu_semantic_forms/tests/test_semantic_forms_models.py","packages/adeu_semantic_forms/tests/test_semantic_forms_parse_profile.py","packages/adeu_semantic_forms/tests/test_semantic_forms_parser.py"],"reference_resolved_singleton_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49b/reference_semantic_parse_result_resolved_singleton.json","reference_typed_alternatives_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49b/reference_semantic_parse_result_typed_alternatives.json","reference_clarification_required_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49b/reference_semantic_parse_result_clarification_required.json","reference_rejected_unsupported_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49b/reference_semantic_parse_result_rejected_unsupported.json","reference_exact_anchor_precedence_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49b/reference_semantic_parse_result_exact_anchor_precedence.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v118/evidence_inputs/metric_key_continuity_assertion_v118.json","runtime_observability_comparison_path":"artifacts/agent_harness/v118/evidence_inputs/runtime_observability_comparison_v118.json","runtime_event_stream_path":"artifacts/agent_harness/v118/runtime/evidence/local/urm_events.ndjson","notes":"v118 evidence pins the released V49-B semantic recovery lane on main: one repo-owned adeu_semantic_forms parser over one released repo_policy_work parse profile, released V49-A parse-result and normal-form outputs only, candidate distinctness by normal_form.semantic_hash only, deterministic alternative ordering, zero-candidate clarification posture, explicit exact-anchor precedence, fail-closed equal-strength conflict handling, preserved multi-effect forbid recovery, deterministic v49b replay fixtures, and no deterministic lowering, V48 bridge helper, or product-surface widening."}
```

## Recommendation (Post v118)

- gate decision:
  - `V49B_SEMANTIC_FORMS_RECOVERY_COMPLETE_ON_MAIN`
  - `V49_SEMANTIC_FORMS_SUBSTRATE_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v118` closes the bounded `V49-B` recovery seam on `main` by shipping the first
    repo-owned `adeu_semantic_forms` parser over the already released `V49-A`
    substrate contracts.
  - the shipped slice remains recovery-first and bounded: one input text, one released
    parse profile, one starter domain, one released parse-result contract, one frozen
    outcome vocabulary, and no lowering, bridge, or product-surface widening.
  - candidate distinctness is explicit and deterministic: dedupe happens only by
    canonical semantic hash, ordering is deterministic before `candidate_rank`
    assignment, and support-only recovery explanations do not change semantic identity.
  - ambiguity and unsupported posture remain typed and fail closed in the shipped
    parser outputs, including zero-candidate clarification and explicit reject posture.
  - exact anchor / exact phrase precedence is explicit, equal-strength conflicts do not
    silently choose, and recovered `forbid_effect` cues preserve all matched effects.
  - the imported prototype bundle remains support-only and non-precedent; the release
    re-authors live parser code in repo-owned package paths rather than importing
    prototype code wholesale.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs `v117` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now records `V49-B` as closed on `main` and
    advances the branch-local default next path to `V49-C` / `vNext+119`.
