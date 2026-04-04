# Draft Stop-Gate Decision (Post vNext+121)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS121.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v121_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+121` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md`.
- This note captures bounded `V50-A` census / coverage evidence only; it does not
  authorize the later semantic-audit ledger, the `V49` primitive reuse-vs-independence
  decision, CLI/API/web consumers, repo-wide scope widening, runtime mutation
  surfaces, or imported-bundle precedent by itself.
- Canonical `V50-A` release in `v121` is carried by the shipped
  `adeu_symbol_audit` package source, committed deterministic `v50a` fixtures, package
  tests, and the canonical `v50a_symbol_census_coverage_evidence@1` evidence input
  under `artifacts/agent_harness/v121/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md` now marks `V50-A`
  closed on `main` and advances the branch-local default next path to `V50-B`; it
  does not select the `V50-B` ledger semantics by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#343` (`feat(v121): add symbol audit census and coverage`)
- arc-completion merge commit: `b4c8d3353ba0f50aeef912b1dea8e1cb343774a9`
- merged-at timestamp: `2026-04-04T02:19:46Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v121_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v121_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v121_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v121/evidence_inputs/metric_key_continuity_assertion_v121.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v121/evidence_inputs/runtime_observability_comparison_v121.json`
  - `V50-A` release evidence input:
    `artifacts/agent_harness/v121/evidence_inputs/v50a_symbol_census_coverage_evidence_v121.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v121/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS121_EDGES.md`

## Exit-Criteria Check (vNext+121)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V50-A` merged with green CI | required | `pass` | PR `#343`, merge commit `b4c8d3353ba0f50aeef912b1dea8e1cb343774a9`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_symbol_audit` package remains the only live owner of the shipped `V50-A` code | required | `pass` | `packages/adeu_symbol_audit/pyproject.toml`, `packages/adeu_symbol_audit/src/adeu_symbol_audit/*.py`, and absence of prototype-tree import into live package paths |
| The first release emits exactly one scope manifest, one deterministic symbol census, and one manifest-to-census coverage report | required | `pass` | `build_reference_architecture_ir_scope_manifest(...)`, `build_symbol_census(...)`, `build_manifest_to_census_coverage_report(...)`, and committed `v50a` fixtures |
| The exact three-file pilot scope is bound to explicit `sha256` values and replays deterministically over committed bytes | required | `pass` | `reference_symbol_audit_scope_manifest.json`, `test_reference_architecture_ir_scope_manifest_matches_fixture`, and `ScopeManifestSourceFile` validation |
| Shared symbol kinds reuse the released textual `symbol:{module_path}:{qualname}:{symbol_kind}` law and `local_function` remains an explicit family-local extension only | required | `pass` | `compute_symbol_audit_symbol_id(...)`, shared-kind parity tests against `adeu_repo_description.models.compute_symbol_id(...)`, and explicit `local_function` fixture/test coverage |
| Census parsing fails closed when live source bytes drift away from the manifest hashes | required | `pass` | `_read_verified_manifest_source_file(...)` in `census.py` and `test_build_symbol_census_rejects_manifest_hash_drift` |
| Coverage remains manifest-to-census closure only and fails closed on missing files, unexpected files, disallowed kinds, duplicate IDs, and manifest-ref mismatch | required | `pass` | `SymbolAuditCoverageReport`, `build_manifest_to_census_coverage_report(...)`, fail-closed coverage tests, and explicit `census_scope_manifest_ref` carrier |
| The package is bootstrapped into the repo Python environment so full-suite CI can import it without local `PYTHONPATH` hacks | required | `pass` | `Makefile` editable-install wiring for `packages/adeu_symbol_audit[dev]` |
| Deterministic `v50a` fixtures replay exactly and prove local-function capture plus typed coverage mismatch posture | required | `pass` | `packages/adeu_symbol_audit/tests/test_symbol_audit_models.py`, `test_symbol_audit_census.py`, `test_symbol_audit_coverage.py`, and committed fixtures under `packages/adeu_symbol_audit/tests/fixtures/v50a/` |
| No semantic audit ledger, semantic evidence vocabulary, CLI surface, repo-wide scope, or prototype import ships in this slice | required | `pass` | shipped scope limited to package/source/tests/fixtures and absence of `spu.py`, `cli.py`, or product consumers |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v121_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v121/evidence_inputs/metric_key_continuity_assertion_v121.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v121/evidence_inputs/runtime_observability_comparison_v121.json` |

## Stop-Gate Summary

```json
{
  "schema": "v121_closeout_stop_gate_summary@1",
  "arc": "vNext+121",
  "target_path": "V50-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v120": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 136,
  "runtime_observability_delta_ms": 29
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v120_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v121_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+120","current_arc":"vNext+121","baseline_source":"artifacts/stop_gate/report_v120_closeout.md","current_source":"artifacts/stop_gate/report_v121_closeout.md","baseline_elapsed_ms":107,"current_elapsed_ms":136,"delta_ms":29,"notes":"v121 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V50-A symbol census and coverage lane: one repo-owned adeu_symbol_audit package, one exact three-file architecture_ir pilot manifest with explicit sha256 binding, one deterministic symbol census, one manifest-to-census coverage report, exact textual symbol-id compatibility for shared kinds, one explicit local_function family-local extension, fail-closed live-byte verification against the manifest before census parsing, fail-closed scope_manifest_ref coverage mismatch detection, deterministic v50a replay fixtures, Makefile bootstrap wiring for the package, and no semantic audit ledger, CLI surface, or repo-wide scope widening."}
```

## V50A Symbol Census Coverage Evidence

```json
{"schema":"v50a_symbol_census_coverage_evidence@1","evidence_input_path":"artifacts/agent_harness/v121/evidence_inputs/v50a_symbol_census_coverage_evidence_v121.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md#v121-continuation-contract-machine-checkable","merged_pr":"#343","merge_commit":"b4c8d3353ba0f50aeef912b1dea8e1cb343774a9","implementation_packages":["adeu_symbol_audit"],"symbol_audit_package_root":"packages/adeu_symbol_audit","symbol_audit_pyproject_path":"packages/adeu_symbol_audit/pyproject.toml","symbol_audit_models_source_path":"packages/adeu_symbol_audit/src/adeu_symbol_audit/models.py","symbol_audit_census_source_path":"packages/adeu_symbol_audit/src/adeu_symbol_audit/census.py","symbol_audit_coverage_source_path":"packages/adeu_symbol_audit/src/adeu_symbol_audit/coverage.py","symbol_audit_package_init_source_path":"packages/adeu_symbol_audit/src/adeu_symbol_audit/__init__.py","repo_bootstrap_makefile_path":"Makefile","test_reference_paths":["packages/adeu_symbol_audit/tests/test_symbol_audit_models.py","packages/adeu_symbol_audit/tests/test_symbol_audit_census.py","packages/adeu_symbol_audit/tests/test_symbol_audit_coverage.py"],"reference_scope_manifest_fixture_path":"packages/adeu_symbol_audit/tests/fixtures/v50a/reference_symbol_audit_scope_manifest.json","reference_census_fixture_path":"packages/adeu_symbol_audit/tests/fixtures/v50a/reference_symbol_census.json","reference_coverage_fixture_path":"packages/adeu_symbol_audit/tests/fixtures/v50a/reference_symbol_audit_coverage_report.json","missing_source_fixture_path":"packages/adeu_symbol_audit/tests/fixtures/v50a/reference_symbol_audit_coverage_report_fail_closed_missing_source_file.json","released_repo_symbol_catalog_reference_path":"apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json","released_repo_symbol_catalog_schema_path":"packages/adeu_repo_description/schema/repo_symbol_catalog.v1.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v121/evidence_inputs/metric_key_continuity_assertion_v121.json","runtime_observability_comparison_path":"artifacts/agent_harness/v121/evidence_inputs/runtime_observability_comparison_v121.json","runtime_event_stream_path":"artifacts/agent_harness/v121/runtime/evidence/local/urm_events.ndjson","notes":"v121 evidence pins the released V50-A symbol census and coverage lane on main: one repo-owned adeu_symbol_audit package over one exact three-file architecture_ir pilot scope, one deterministic scope manifest with explicit file sha256 binding, one deterministic AST-first symbol census, one manifest-to-census coverage report, shared textual symbol-id law compatibility for class/function/method, one explicit local_function family-local extension, fail-closed manifest-byte verification before parsing, fail-closed manifest-ref mismatch detection in coverage, deterministic v50a replay fixtures, repo bootstrap wiring for editable package installation, and no semantic audit ledger, CLI surface, or repo-wide scope widening."}
```

## Recommendation (Post v121)

- gate decision:
  - `V50A_SYMBOL_CENSUS_COVERAGE_COMPLETE_ON_MAIN`
  - `V50_SYMBOL_AUDIT_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v121` closes the bounded `V50-A` census / coverage seam on `main` by shipping
    the first repo-owned `adeu_symbol_audit` package over one exact
    `packages/adeu_architecture_ir` pilot scope.
  - the shipped slice remains read-only and bounded: one explicit scope manifest,
    one deterministic AST-first census, one manifest-to-census closure report, one
    shared textual symbol-id law for shared kinds, one explicit `local_function`
    family-local extension, and no semantic ledger or consumer widening.
  - admissibility is explicit and fail closed: live source bytes must still match the
    manifest before parsing, coverage now rejects stale or mismatched manifest/census
    pairings, and disallowed symbol kinds or duplicate IDs remain typed mismatch
    carriers instead of ambient errors.
  - overlap with released `repo_symbol_catalog@1` remains explicit and non-superseding:
    shared kinds reuse the released textual identity law, while `local_function`
    remains one family-local extension only.
  - the imported prototype bundle remains support-only and non-precedent; the release
    re-authors live code in repo-owned package paths rather than importing prototype
    code wholesale.
  - the repo bootstrap flow now installs the package, clearing the full-suite Python CI
    import path without introducing any new runtime or product surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+29 ms` vs `v120` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md` should now be read with `V50-A` closed on
    `main` and the branch-local default next path advanced to `V50-B` / `vNext+122`.
