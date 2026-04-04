# Assessment vNext+121 Edges

Status: post-closeout edge assessment for `V50-A` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS121_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Silent Fork Of `repo_symbol_catalog@1`

- Risk:
  the family could claim simple overlap with released `repo_symbol_catalog@1` while
  actually redefining shared identity or symbol-kind meaning.
- Response:
  keep the overlap law explicit, reuse the released textual symbol-id law for shared
  kinds only, and keep `local_function` as one non-superseding family-local extension.
- Closeout Evidence:
  `compute_symbol_audit_symbol_id(...)` in
  `packages/adeu_symbol_audit/src/adeu_symbol_audit/models.py`,
  shared-kind parity tests against `adeu_repo_description.models.compute_symbol_id`,
  and committed `v50a` fixtures.

### Edge 2: Hidden `local_function` Laundering

- Risk:
  `local_function` could drift into an implicit claim that the released descriptive
  baseline already contains that kind.
- Response:
  keep `local_function` explicit, family-local, and textual-shape-compatible only.
- Closeout Evidence:
  frozen `DEFAULT_SYMBOL_KINDS`, `REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES`,
  and local-function capture tests in `test_symbol_audit_census.py`.

### Edge 3: Pilot-Scope Byte Drift

- Risk:
  the census could be treated as if it were grounded in an exact manifest while
  actually reading later live bytes from disk.
- Response:
  bind the manifest to explicit `sha256` values and reject any live-byte mismatch
  before parsing.
- Closeout Evidence:
  `ScopeManifestSourceFile`, `_read_verified_manifest_source_file(...)`, and
  `test_build_symbol_census_rejects_manifest_hash_drift`.

### Edge 4: Manifest/Census Pairing Drift

- Risk:
  a census built for one manifest could be replayed against a different manifest and
  still receive a clean coverage report.
- Response:
  carry both `scope_manifest_ref` and `census_scope_manifest_ref` in the typed
  coverage surface and fail closed when they diverge.
- Closeout Evidence:
  `SymbolAuditCoverageReport`, `build_manifest_to_census_coverage_report(...)`, and
  `test_scope_manifest_ref_mismatch_fails_closed`.

### Edge 5: Missing-Manifest Drift

- Risk:
  manifest files could disappear from the observed census source set without one typed
  mismatch carrier.
- Response:
  keep `missing_source_files` explicit and make it part of the fail-closed coverage
  status law.
- Closeout Evidence:
  `reference_symbol_audit_coverage_report_fail_closed_missing_source_file.json` and
  `test_missing_manifest_source_file_fails_closed_with_typed_carrier`.

### Edge 6: Coverage Drift Into Semantic Audit

- Risk:
  the first coverage implementation could quietly adopt audit-ledger completion or
  low-confidence semantics from the prototype.
- Response:
  freeze `V50-A` coverage as manifest-to-census closure only and defer semantic audit
  completion semantics entirely to `V50-B`.
- Closeout Evidence:
  shipped coverage surface limited to source-file/kind/identity closure carriers and
  absence of `spu.py` or audit-status logic from the live package.

### Edge 7: Non-Deterministic Census Ordering

- Risk:
  AST traversal or incidental iteration order could make census replay unstable over
  the same exact bytes.
- Response:
  require deterministic sorting, contiguous census indices, and fixture replay.
- Closeout Evidence:
  `build_symbol_census(...)`, `SymbolCensus` contiguous-index validation, and exact
  replay tests against `reference_symbol_census.json`.

### Edge 8: CI Import-Path Drift

- Risk:
  the bounded package could pass only under local `PYTHONPATH` overrides while failing
  full repo test collection on CI.
- Response:
  wire the package into the repo bootstrap/editable-install path.
- Closeout Evidence:
  `Makefile` editable-install entry for `packages/adeu_symbol_audit[dev]` and green
  merged `python` CI on PR `#343`.

### Edge 9: Semantic-Primitive Prematurity

- Risk:
  the first B-track slice could accidentally decide whether later semantic audit
  vocabulary reuses `V49` primitives or remains intentionally independent.
- Response:
  keep `V50-A` artifacts semantically minimal enough that either `V50-B` choice
  remains open.
- Closeout Evidence:
  shipped scope limited to manifest/census/coverage only, with no semantic audit entry
  schema or confidence-band ledger in the live package.

### Edge 10: Consumer Prematurity

- Risk:
  semantic audit, CLI, API, or web consumers could leak into the first read-only slice
  and blur family ownership.
- Response:
  keep `V50-A` bounded to package scaffold, contracts, fixtures, bootstrap wiring, and
  targeted tests only.
- Closeout Evidence:
  implementation footprint limited to
  `packages/adeu_symbol_audit/src/adeu_symbol_audit/`,
  `packages/adeu_symbol_audit/tests/`, the `Makefile` bootstrap edit, and closeout
  artifacts only.

## Current Judgment

- `V50-A` was the right first B-track move because it froze the read-only symbol
  universe, exact pilot-scope manifest law, and closure report law before the repo
  accepted any semantic audit claims.
- the shipped result is properly narrow: one repo-owned `adeu_symbol_audit` package,
  one exact three-file pilot scope, explicit `sha256` manifest binding, deterministic
  symbol census, manifest-to-census closure only, explicit `local_function`
  family-local extension, fail-closed manifest-byte and manifest-ref mismatch checks,
  deterministic `v50a` fixture replay, and no semantic-audit ledger or consumer
  widening.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v33.md` should now be read with `V50-A` closed on
  `main` and the branch-local default next path advanced to `V50-B` / `vNext+122`.
