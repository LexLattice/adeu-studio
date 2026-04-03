# Draft Stop-Gate Decision (Post vNext+117)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS117.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v117_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+117` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md`.
- This note captures bounded `V49-A` semantic substrate contract evidence only; it
  does not authorize `NL -> ADEU` recovery, deterministic lowering, `V48` bridge
  behavior, CLI/API/web consumers, multi-domain semantic expansion, or intake-bundle
  precedent by itself.
- Canonical `V49-A` release in `v117` is carried by the shipped
  `adeu_semantic_forms` source, committed deterministic fixtures, package bootstrap
  integration, and the canonical `v49a_semantic_forms_core_evidence@1` evidence input
  under `artifacts/agent_harness/v117/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now marks `V49-A`
  closed on `main` and advances the branch-local default next path to `V49-B`; it
  does not select any later `V49` closeout by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#339` (`[codex] add V49-A semantic forms core contracts`)
- arc-completion merge commit: `4da1276ed8c088d10ae0bda46442e2de0d96b7ae`
- merged-at timestamp: `2026-04-03T22:20:10Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v117_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v117_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v117_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v117/evidence_inputs/metric_key_continuity_assertion_v117.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v117/evidence_inputs/runtime_observability_comparison_v117.json`
  - `V49-A` release evidence input:
    `artifacts/agent_harness/v117/evidence_inputs/v49a_semantic_forms_core_evidence_v117.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v117/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS117_EDGES.md`

## Exit-Criteria Check (vNext+117)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V49-A` merged with green CI | required | `pass` | PR `#339`, merge commit `4da1276ed8c088d10ae0bda46442e2de0d96b7ae`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_semantic_forms` package is the only live implementation owner for the first semantic substrate slice | required | `pass` | `packages/adeu_semantic_forms/pyproject.toml`, `packages/adeu_semantic_forms/src/adeu_semantic_forms/`, and absence of prototype-tree import into live package paths |
| Released `V49-A` schema family is frozen exactly to parse-profile, statement-core, normal-form, parse-result, and transform-contract contracts | required | `pass` | constants and exported models in `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py` and `packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py` |
| Starter domain remains exactly `repo_policy_work` | required | `pass` | `build_reference_repo_policy_work_profile()` in `packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py` and committed profile fixture |
| Canonical semantic identity law remains bounded to identity-only fields while projection/support fields do not affect semantic hash | required | `pass` | `IDENTITY_FIELD_NAMES`, `PROJECTION_FIELD_NAMES`, semantic-hash validators in `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and fixture tests in `packages/adeu_semantic_forms/tests/test_semantic_forms_models.py` |
| Parse-result outcome vocabulary is frozen and fail-closed | required | `pass` | `ParseStatus` plus parse-result validators in `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, committed accepted/reject fixtures, and tests in `packages/adeu_semantic_forms/tests/test_semantic_forms_models.py` |
| Accepted and mutation/reject fixtures replay deterministically | required | `pass` | fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49a/` plus `packages/adeu_semantic_forms/tests/test_semantic_forms_models.py` and `packages/adeu_semantic_forms/tests/test_semantic_forms_parse_profile.py` |
| Repo-wide canonical JSON inventory explicitly records the new semantic-forms helper surface | required | `pass` | `apps/api/tests/test_canonical_json_conformance_vnext_plus27.py` updated for `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py::{canonical_json,sha256_canonical_json}` |
| Support-only external intake remains non-live in default lint/test collection | required | `pass` | `extend-exclude = [\"examples/external_prototypes\"]` and `norecursedirs = [\"examples/external_prototypes\"]` in `pyproject.toml` |
| No parser behavior, lowering behavior, `V48` bridge behavior, or product consumer surface ships in this slice | required | `pass` | implementation footprint limited to `models.py`, `parse_profile.py`, package init, fixtures, tests, bootstrap hook, and absence of parser/bridge/product files under `packages/adeu_semantic_forms` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v117_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v117/evidence_inputs/metric_key_continuity_assertion_v117.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v117/evidence_inputs/runtime_observability_comparison_v117.json` |

## Stop-Gate Summary

```json
{
  "schema": "v117_closeout_stop_gate_summary@1",
  "arc": "vNext+117",
  "target_path": "V49-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v116": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 107,
  "runtime_observability_delta_ms": -32
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v116_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v117_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+116","current_arc":"vNext+117","baseline_source":"artifacts/stop_gate/report_v116_closeout.md","current_source":"artifacts/stop_gate/report_v117_closeout.md","baseline_elapsed_ms":139,"current_elapsed_ms":107,"delta_ms":-32,"notes":"v117 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V49-A semantic substrate contract lane: one repo-owned adeu_semantic_forms package, one bounded repo_policy_work starter domain, frozen statement-core/relation/lane/object vocabularies, canonical identity and hash law over identity-only fields, explicit projection/support exclusions, typed ambiguity and rejected_unsupported posture, deterministic reference and mutation fixtures, explicit canonical helper inventory registration, and no parser behavior, lowering behavior, V48 bridge behavior, or product-surface widening."}
```

## V49A Semantic Forms Core Evidence

```json
{"schema":"v49a_semantic_forms_core_evidence@1","evidence_input_path":"artifacts/agent_harness/v117/evidence_inputs/v49a_semantic_forms_core_evidence_v117.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS117.md#v117-continuation-contract-machine-checkable","merged_pr":"#339","merge_commit":"4da1276ed8c088d10ae0bda46442e2de0d96b7ae","implementation_packages":["adeu_semantic_forms"],"semantic_forms_package_root":"packages/adeu_semantic_forms","semantic_forms_pyproject_path":"packages/adeu_semantic_forms/pyproject.toml","semantic_forms_models_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py","semantic_forms_parse_profile_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py","semantic_forms_package_init_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py","bootstrap_integration_path":"Makefile","canonical_helper_guard_test_path":"apps/api/tests/test_canonical_json_conformance_vnext_plus27.py","test_reference_paths":["packages/adeu_semantic_forms/tests/test_semantic_forms_models.py","packages/adeu_semantic_forms/tests/test_semantic_forms_parse_profile.py","apps/api/tests/test_canonical_json_conformance_vnext_plus27.py"],"reference_parse_profile_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_parse_profile.json","reference_statement_core_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_statement_core.json","reference_normal_form_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_normal_form.json","reference_parse_result_resolved_singleton_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_parse_result_resolved_singleton.json","reference_parse_result_typed_alternatives_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_parse_result_typed_alternatives.json","reference_parse_result_rejected_unsupported_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_parse_result_rejected_unsupported.json","reference_transform_contract_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reference_semantic_transform_contract.json","projection_only_mutation_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/mutation_semantic_normal_form_projection_only.json","identity_change_mutation_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/mutation_semantic_normal_form_identity_change.json","rejected_invalid_status_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49a/reject_invalid_parse_result_status.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v117/evidence_inputs/metric_key_continuity_assertion_v117.json","runtime_observability_comparison_path":"artifacts/agent_harness/v117/evidence_inputs/runtime_observability_comparison_v117.json","runtime_event_stream_path":"artifacts/agent_harness/v117/runtime/evidence/local/urm_events.ndjson","notes":"v117 evidence pins the released V49-A semantic substrate contract lane on main: one repo-owned adeu_semantic_forms package, starter domain repo_policy_work, frozen statement-core/relation/lane/object vocabularies, canonical semantic identity and hash law over relation_kind plus object_value only, explicit projection/support exclusions, typed parse-result outcome vocabulary, deterministic reference and mutation fixtures, fail-closed alias and parse-result validation, support-only intake preservation without prototype-tree import, default test-discovery exclusion for support-only external prototype intake, and explicit canonical helper inventory registration in the repo-wide vnext+27 conformance guard."}
```

## Recommendation (Post v117)

- gate decision:
  - `V49A_SEMANTIC_FORMS_CORE_CONTRACTS_COMPLETE_ON_MAIN`
  - `V49_SEMANTIC_FORMS_SUBSTRATE_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v117` closes the bounded `V49-A` substrate-contract seam on `main` by shipping
    the first repo-owned `adeu_semantic_forms` package and freezing the starter
    semantic contract family around `repo_policy_work`.
  - the shipped slice remains contract-first and substrate-first: one parse profile,
    one statement-core contract, one normal-form contract, one parse-result contract,
    one transform-contract surface, one frozen starter-domain posture, and no parser
    behavior, lowering behavior, bridge behavior, or product-surface widening.
  - semantic identity is explicit and bounded: only identity fields participate in the
    canonical semantic hash, while support/projection fields are validated but do not
    change semantic identity.
  - ambiguity and unsupported posture are both typed and fail closed in the shipped
    parse-result contracts.
  - the imported prototype bundle remains support-only and non-precedent; the release
    re-authors live package code rather than importing prototype code wholesale.
  - the repo-wide canonical helper inventory and default lint/test collection posture
    were both updated explicitly so the new package is recorded in live conformance
    surfaces while the support-only prototype intake stays out of default CI
    collection.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`-32 ms` vs `v116`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now records `V49-A` as closed on `main` and
    advances the branch-local default next path to `V49-B` / `vNext+118`.
