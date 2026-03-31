# Assessment vNext+101 Edges

Status: post-closeout edge assessment for `V45-B` (March 31, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS101_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Symbol-As-Authority Drift

- Risk:
  symbol-catalog outputs could be overread as refactor or scheduling authority.
- Response:
  keep symbol and dependency outputs descriptive-first and non-promotional.
- Closeout Evidence:
  `graph_scope` authority-laundering checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reject_refactor_entitlement_laundering.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45b.py`.

### Edge 2: Dangling Dependency Laundering

- Risk:
  dependency edges could reference unknown symbol or module targets while still
  appearing valid, or collapse several endpoint kinds into one untyped ref string.
- Response:
  fail closed on any edge whose internal endpoints are not present in typed symbol or
  declared internal module-boundary surfaces, and require explicit endpoint kinds for
  boundary targets.
- Closeout Evidence:
  pair validation in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus101/repo_dependency_graph_v101_reject_dangling_symbol_ref.json`,
  and rejection assertions in
  `packages/adeu_repo_description/tests/test_repo_description_v45b.py`.

### Edge 3: Symbol-Role Overclaim

- Risk:
  symbol-role classifications could collapse into vague naming heuristics or unstated
  assumptions about implementation importance.
- Response:
  require explicit role-classification posture and classification method on typed symbol
  entries.
- Closeout Evidence:
  required symbol entry fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and accepted fixture
  `apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json`.

### Edge 4: Snapshot Overread

- Risk:
  one snapshot-bound symbol/dependency graph could be overread as current repo truth
  after repo drift.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical.
- Closeout Evidence:
  snapshot identity/hash and validity posture fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and accepted fixtures under
  `apps/api/fixtures/repo_description/vnext_plus101/`.

### Edge 5: Provenance Regression Relative To `V102`

- Risk:
  `V45-B` could regress below the provenance rigor added in the `V45-C` hardening pass
  by omitting `source_set_hash`, top-level extraction posture/method, or per-row source
  and derivation anchors.
- Response:
  carry forward explicit source-set hash, top-level extraction posture/method, per-symbol
  source artifact refs, and per-edge derivation posture/method.
- Closeout Evidence:
  `source_set_hash`, `extraction_posture`, `extraction_method`,
  `source_artifact_refs`, `derivation_posture`, and `derivation_method` fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and accepted v101 fixtures.

### Edge 6: Cross-Artifact Drift

- Risk:
  the symbol catalog and dependency graph could each validate independently while
  drifting across snapshot identity, source-set identity, or internal endpoint
  resolution.
- Response:
  require the emitted pair to reconcile over the same snapshot/source-set binding and
  require internal graph endpoints to resolve against the emitted symbol catalog or the
  declared internal module-boundary namespace.
- Closeout Evidence:
  `validate_repo_symbol_catalog_dependency_graph_pair` in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  accepted fixtures
  `repo_symbol_catalog_v101_reference.json` and
  `repo_dependency_graph_v101_reference.json`,
  and reject pair fixture
  `repo_symbol_dependency_pair_v101_reject_mismatched_snapshot_source_identity.json`.

### Edge 7: Whole-Repo And Cross-Language Scope Creep

- Risk:
  the first code-graph seam could widen early into whole-repo exhaustive or
  multi-language inventory work.
- Response:
  keep `v101` bounded to one explicit Python source-set posture only.
- Closeout Evidence:
  bounded source-set extraction in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  via `default_v45b_source_paths()`
  and accepted fixture source-set bindings in
  `apps/api/fixtures/repo_description/vnext_plus101/`.

### Edge 8: Boundary Endpoint Ambiguity

- Risk:
  legitimate stdlib, third-party, or otherwise out-of-scope dependencies could be
  either rejected incorrectly or silently accepted as dangling strings if boundary
  typing remains implicit.
- Response:
  make external or out-of-scope dependencies explicit through bounded endpoint-kind and
  dependency-posture vocabularies rather than leaving them untyped.
- Closeout Evidence:
  endpoint-kind and dependency-posture fields in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`,
  reject fixture
  `apps/api/fixtures/repo_description/vnext_plus101/repo_dependency_graph_v101_reject_out_of_scope_endpoint_without_boundary_typing.json`,
  and external dotted-ref normalization in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`.

### Edge 9: Test-Intent Laundering

- Risk:
  typed code-graph outputs could be overread as test-intent or invariant-binding
  doctrine.
- Response:
  defer test-intent matrix release to later `V45-D` work.
- Closeout Evidence:
  `V45-B` lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS101.md`
  and absence of test-intent artifacts in the shipped v101 surface set.

### Edge 10: Optimization Entitlement Creep

- Risk:
  hotspot or dependency concentration signals could be interpreted as automatic split,
  abstraction, or optimization entitlement.
- Response:
  keep `V45-B` descriptive-only and defer optimization-register doctrine to `V45-E`.
- Closeout Evidence:
  descriptive-only `graph_scope` checks in
  `packages/adeu_repo_description/src/adeu_repo_description/models.py`
  and absence of optimization-register artifacts in the shipped v101 surface set.

### Edge 11: AST Completeness Drift

- Risk:
  symbol or dependency extraction could silently miss unpacking assignments, nested
  control-flow definitions, or nested control-flow imports.
- Response:
  recurse through bounded control-flow statement bodies and expand assignment-target
  extraction beyond simple `ast.Name` bindings.
- Closeout Evidence:
  recursive assignment/control-flow handling in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and tests
  `test_v45b_collects_unpacking_targets_and_control_flow_symbols` plus
  `test_v45b_collects_nested_control_flow_imports`.

### Edge 12: Normalized Module-Path Collision

- Risk:
  two bounded source paths could normalize to the same Python import path and silently
  overwrite each other in module-boundary resolution.
- Response:
  reject duplicate normalized module import paths fail-closed during source-set
  ingestion.
- Closeout Evidence:
  duplicate module-import-path guard in
  `packages/adeu_repo_description/src/adeu_repo_description/extract.py`
  and test
  `test_v45b_rejects_duplicate_normalized_module_import_paths`.

## Current Judgment

- `V45-B` on `main` resolves the bounded code-self-description gap by shipping
  deterministic `repo_symbol_catalog@1` and `repo_dependency_graph@1` surfaces with
  explicit endpoint ontology, explicit snapshot/source provenance, and explicit
  pair-consistency rules.
- the shipped baseline remains descriptive-first and non-promotional, preserving
  deferral of `V45-D`, `V45-E`, `V45-F`, scheduler automation, mutation entitlement,
  and recursive-governance binding.
